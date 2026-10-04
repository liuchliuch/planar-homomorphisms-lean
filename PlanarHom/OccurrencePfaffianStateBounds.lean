import PlanarHom.OccurrencePfaffianEvaluationProgram
import PlanarHom.MaterializedFieldListMachines

/-! NEW reconstruction. Literal list-code estimates and the actual scalar
factor transcript of the pivot machine. These lemmas connect minor-based
entry heights to full serialized-state heights, rather than assuming an
arithmetic-cost oracle. -/
namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines ListFlattenMachines

 theorem list_encoding_bound {A : Type} (e : BitEncoding A) (xs : List A)
    (N B : ℕ) (hn : xs.length ≤ N) (hb : ∀ a ∈ xs, (e.encode a).length ≤ B) :
    (e.list.encode xs).length ≤ 3*(2*N*B+N)+1 := by
  have hs := (ListMapMachines.sum_map_le_mul (fun a => (e.encode a).length) xs B hb).trans
    (Nat.mul_le_mul_right B hn)
  have hw := word_length_le_payload e xs
  rw [payloadSize_eq] at hw
  nlinarith

 theorem grid_encoding_bound {A : Type} (e : BitEncoding A) (g : List (List A))
    (N B : ℕ) (hn : g.length ≤ N) (hrows : ∀ r ∈ g, r.length ≤ N)
    (hb : ∀ r ∈ g, ∀ a ∈ r, (e.encode a).length ≤ B) :
    (e.list.list.encode g).length ≤ 3*(2*N*(3*(2*N*B+N)+1)+N)+1 := by
  exact list_encoding_bound e.list g N _ hn
    (fun r hr => list_encoding_bound e r N B (hrows r hr) (hb r hr))

variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

def stepFactor (s : State K) : K :=
  if s.2.1 = [] then 1 else
    if pivotCandidates s = [] then 0 else
      sign (pivotChoice s).2 * entry s.1 (headVertex s) (pivotChoice s).1

 theorem step_accumulator (s : State K) : (step s).2.2 = s.2.2 * stepFactor s := by
  unfold step stepFactor
  split_ifs <;> simp_all [pivotStep]

/-- Factors are recorded from the actual successive states, not arbitrary
field values or a guessed expression DAG. -/
def factorTrace (s : State K) (t : ℕ) : List K :=
  (List.range t).map (fun i => stepFactor (step^[i] s))

 theorem accumulator_eq_product (s : State K) (t : ℕ) :
    (step^[t] s).2.2 = s.2.2 * (factorTrace s t).prod := by
  induction t with
  | zero => simp [factorTrace]
  | succ t ih =>
    rw [Function.iterate_succ_apply', step_accumulator, ih]
    simp [factorTrace, List.range_succ, mul_assoc]

 theorem factorTrace_length (s : State K) (t : ℕ) : (factorTrace s t).length = t := by
  simp [factorTrace]

 theorem factorTrace_mem (s : State K) (t : ℕ) (x : K) :
    x ∈ factorTrace s t ↔ ∃ i < t, stepFactor (step^[i] s) = x := by
  simp [factorTrace]

/-- Materialized polynomially many bounded factors have a polynomially bounded
product in the existing exact number-field encoding. -/
 theorem exists_product_encoding_polynomial :
    ∃ p : Polynomial ℕ, ∀ (xs : List K) (N B : ℕ), xs.length ≤ N →
      (∀ x ∈ xs, ((numberFieldEncoding basis).encode x).length ≤ B) →
      ((numberFieldEncoding basis).encode xs.prod).length ≤ p.eval (N+B) := by
  obtain ⟨data⟩ := IntegerCoordinateBounds.exists_clearedCoordinates basis
    (fun k : Fin dimension => basis k)
  let p := (EncodingSizeBounds.coordinateOutputPolynomial dimension
    (MaterializedFieldHeights.heightBase data) (MaterializedFieldHeights.heightBase data)).comp
    ((Polynomial.X+Polynomial.C 2)^2)
  refine ⟨p, fun xs N B hn hb => ?_⟩
  have hh := (MaterializedFieldHeights.list_values_encoding_bound data xs (N+B)
    (by omega) (fun x hx => (hb x hx).trans (by omega))).1
  simpa only [p, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_C] using hh

end PlanarHom.PfaffianList
