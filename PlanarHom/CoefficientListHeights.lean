import PlanarHom.LagrangeCoefficientHeights
import PlanarHom.GraphParallelCode

/-! Polynomial bit-size of complete coefficient lists at every Lagrange construction prefix. -/

noncomputable section
open scoped BigOperators
namespace PlanarHom.CoefficientListHeights
open Complexity LagrangeCoefficientHeights

/-- Actual list framing adds a linear header and two bits per payload bit. -/
theorem list_encoding_length_le {A : Type} (e : BitEncoding A) (xs : List A) (H : ℕ)
    (h : ∀ x ∈ xs, (e.encode x).length ≤ H) :
    (e.list.encode xs).length ≤ (2 * H + 3) * xs.length + 1 := by
  have hf : (BitEncoding.frames (xs.map e.encode)).length ≤ (2 * H + 1) * xs.length := by
    induction xs with
    | nil => simp [BitEncoding.frames]
    | cons x xs ih =>
      have hx := h x (by simp)
      have hs := ih (fun y hy => h y (by simp [hy]))
      simp only [List.map_cons, BitEncoding.frames, List.length_append, BitEncoding.frame_length,
        List.length_cons]
      nlinarith
  have hn := Complexity.encodeNat_length_le xs.length
  simp only [BitEncoding.list, List.length_append, BitEncoding.frame_length]
  nlinarith

/-- A polynomial bound for the complete coefficient vector, including its canonical header. -/
theorem exists_polynomial_coefficient_list_length_bound
    {K I : Type} [Field K] [Algebra ℚ K] [Fintype I] {dimension : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (A : I → K) :
    ∃ p : Polynomial ℕ, ∀ (N m : ℕ) (words : Fin N → List I),
      (∀ i, (words i).length = m) →
      (((numberFieldEncoding basis).list).encode
        (List.ofFn (fun k : Fin (N + 1) =>
          (∏ i, (Polynomial.X - Polynomial.C (((words i).map A).prod))).coeff k.val))).length ≤
        p.eval (N * (m + 1) + 1) := by
  obtain ⟨p, hp⟩ := exists_polynomial_coefficient_length_bound basis A
  refine ⟨(Polynomial.C 2 * p + Polynomial.C 3) * Polynomial.X + Polynomial.C 1, ?_⟩
  intro N m words hlen
  let L := N * (m + 1) + 1
  have hcoeff : ∀ x ∈ List.ofFn (fun k : Fin (N + 1) =>
      (∏ i, (Polynomial.X - Polynomial.C (((words i).map A).prod))).coeff k.val),
      ((numberFieldEncoding basis).encode x).length ≤ p.eval L := by
    intro x hx
    obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hx
    exact hp N m words hlen k.val
  have hlist := list_encoding_length_le (numberFieldEncoding basis) _ (p.eval L) hcoeff
  rw [List.length_ofFn] at hlist
  have hN : N + 1 ≤ L := by dsimp [L]; nlinarith
  have hb := hlist.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hN) 1)
  simpa only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X] using hb

end PlanarHom.CoefficientListHeights
