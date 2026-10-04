import PlanarHom.OccurrencePfaffianIterationInvariant

/-! NEW reconstruction. A polynomial in the literal original nested-list code
bounds every live matrix, active label and scalar accumulator of the real loop. -/
namespace PlanarHom.PfaffianList
open Complexity MultiGraph.PfaffianElimination MachineComposition Polynomial
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

 theorem exists_accumulator_encoding_polynomial :
    ∃ p : Polynomial ℕ, ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
      (∀ i j, A j i = -A i j) → (∀ i, A i i = 0) → ∀ t, t ≤ n →
      ((numberFieldEncoding basis).encode (step^[t] (initialState (matrixRows A))).2.2).length ≤
        p.eval (PfaffianMinorHeights.matrixInputLength basis A) := by
  obtain ⟨q,hq⟩ := exists_factor_encoding_polynomial basis
  obtain ⟨r,hr⟩ := exists_product_encoding_polynomial basis
  refine ⟨r.comp (X+q), fun A hskew hdiag t ht => ?_⟩
  let s := initialState (matrixRows A)
  let N := PfaffianMinorHeights.matrixInputLength basis A
  have hn : t ≤ N := ht.trans (PfaffianMinorHeights.dimension_le_matrixInputLength basis A)
  have hf : ∀ x ∈ factorTrace s t, ((numberFieldEncoding basis).encode x).length ≤ q.eval N := by
    intro x hx
    obtain ⟨i,hi,rfl⟩ := (factorTrace_mem s t x).mp hx
    exact hq A _ (matrixState_iterate A hskew hdiag i)
  have hh := hr (factorTrace s t) N (q.eval N) (by simpa [factorTrace_length] using hn) hf
  rw [accumulator_eq_product]
  simpa only [initialState, one_mul, eval_comp, eval_add, eval_X] using hh

 theorem exists_iteration_state_encoding_polynomial :
    ∃ p : Polynomial ℕ, ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
      (∀ i j, A j i = -A i j) → (∀ i, A i i = 0) → ∀ t, t ≤ n →
      ((stateEncoding basis).encode (step^[t] (initialState (matrixRows A)))).length ≤
        p.eval (PfaffianMinorHeights.matrixInputLength basis A) := by
  obtain ⟨q,hq⟩ := exists_polynomial_schur_entry_bound basis
  obtain ⟨r,hr⟩ := exists_accumulator_encoding_polynomial basis
  let pg : Polynomial ℕ := C 3*(C 2*X*(C 3*(C 2*X*q+X)+1)+X)+1
  let pa : Polynomial ℕ := C 3*(C 2*X*X+X)+1
  let p := C 2*pg + C 2*pa + r + C 2
  refine ⟨p, fun A hskew hdiag t ht => ?_⟩
  let N := PfaffianMinorHeights.matrixInputLength basis A
  have hn : _ ≤ N := PfaffianMinorHeights.dimension_le_matrixInputLength basis A
  let s := step^[t] (initialState (matrixRows A))
  obtain ⟨B,active,hg,hx,hvalid,hschur⟩ := matrixState_iterate A hskew hdiag t
  have hgrid : ((gridEncoding basis).encode s.1).length ≤ pg.eval N := by
    change ((gridEncoding basis).encode (step^[t] (initialState (matrixRows A))).1).length ≤ _
    rw [hg]
    have hh := grid_encoding_bound (numberFieldEncoding basis) (matrixRows B) N (q.eval N)
      (by simpa using hn)
      (by intro row hrow; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow; simpa using hn)
      (by
        intro row hrow x hx
        obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hrow
        obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
        exact hq A B active hschur i j)
    simpa only [pg,eval_add,eval_mul,eval_C,eval_X,eval_one] using hh
  have hactive : (BitEncoding.nat.list.encode s.2.1).length ≤ pa.eval N := by
    change (BitEncoding.nat.list.encode (step^[t] (initialState (matrixRows A))).2.1).length ≤ _
    rw [hx]
    have hl : active.length ≤ N := by
      have hh := hvalid.2.2.length_le_card
      simp only [Fintype.card_fin] at hh
      exact hh.trans hn
    have hh := list_encoding_bound BitEncoding.nat (active.map Fin.val) N N
      (by simpa using hl) (by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
        exact (encodeNat_length_le i.val).trans (i.isLt.le.trans hn))
    simpa only [pa,eval_add,eval_mul,eval_C,eval_X,eval_one] using hh
  have hacc : ((numberFieldEncoding basis).encode s.2.2).length ≤ r.eval N :=
    hr A hskew hdiag t ht
  change ((stateEncoding basis).encode s).length ≤ p.eval N
  simp only [stateEncoding,BitEncoding.prod_length]
  simp only [p,eval_add,eval_mul,eval_C]
  omega

end PlanarHom.PfaffianList
