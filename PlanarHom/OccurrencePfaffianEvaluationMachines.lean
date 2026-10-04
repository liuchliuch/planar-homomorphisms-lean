import PlanarHom.OccurrencePfaffianIterationBounds
import PlanarHom.RestrictedIterationMachine
import PlanarHom.PfaffianPivotSemantics

/-! NEW reconstruction. The total runtime-dimensional evaluator is an actual
polynomial-time TM2 under the exact nested-list number-field codec. The bound
uses original-input determinant minors, initialized and preserved through the
literal loop. No cost oracle, assumed FP evaluator or assumed height bound is
an input to this theorem. -/
noncomputable section
open Classical
namespace PlanarHom.PfaffianList
open Complexity PairProjectionMachines MachineComposition
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

 theorem normalizeGrid_idempotent (g : Grid K) : normalizeGrid (normalizeGrid g) = normalizeGrid g := by
  rw [normalizeGrid_eq_matrixRows g]
  exact normalizeGrid_matrixRows _ (fun i j => skewEntry_swap g i.val j.val)
    (fun i => skewEntry_diag g i.val)

abbrev AlternatingGrid (K : Type) [Field K] := {g : Grid K // normalizeGrid g = g}

noncomputable def alternatingEncoding : BitEncoding (AlternatingGrid K) :=
  (gridEncoding basis).restrict (fun g => normalizeGrid g = g)

def prepareGrid (g : Grid K) : AlternatingGrid K := ⟨normalizeGrid g,normalizeGrid_idempotent g⟩

 theorem fp_prepareGrid : FP (gridEncoding basis) (alternatingEncoding basis) (prepareGrid (K := K)) :=
  (fp_normalizeGrid basis).transportOutput (fun _ => rfl)

/-- The physically assembled unary count and initial state, restricted to a
mathematically normalized input. Its inverse is used only to define the codec. -/
noncomputable def loopEncoding : BitEncoding (AlternatingGrid K) :=
  (BitEncoding.unaryNat.prod (stateEncoding basis)).retract
    (fun g => (g.val.length,initialState g.val))
    (fun p => prepareGrid p.2.1)
    (by intro g; apply Subtype.ext; exact g.property)

 theorem fp_prepareLoop : FP (alternatingEncoding basis) (loopEncoding basis) id := by
  have hn : FP (alternatingEncoding basis) BitEncoding.unaryNat
      (fun g : AlternatingGrid K => g.val.length) := (ListUnaryLengthMachine.fp_length (numberFieldEncoding basis).list).transportInput
    (Subtype.val : AlternatingGrid K → Grid K) (fun _ => rfl)
  have hs : FP (alternatingEncoding basis) (stateEncoding basis)
      (fun g : AlternatingGrid K => initialState g.val) := (fp_initialState basis).transportInput
    (Subtype.val : AlternatingGrid K → Grid K) (fun _ => rfl)
  exact (hn.pair hs).transportOutput (fun _ => rfl)

 theorem fp_evaluateAlternating : FP (alternatingEncoding basis) (numberFieldEncoding basis)
    (fun g : AlternatingGrid K => evaluateRawGrid g.val) := by
  obtain ⟨p,hp⟩ := exists_iteration_state_encoding_polynomial basis
  obtain ⟨body⟩ := fp_step basis
  have hsize (g : AlternatingGrid K) (t : ℕ) (ht : t ≤ g.val.length) :
      ((stateEncoding basis).encode (step^[t] (initialState g.val))).length ≤
        p.eval ((loopEncoding basis).encode g).length := by
    let A : Matrix (Fin g.val.length) (Fin g.val.length) K := fun i j => skewEntry g.val i.val j.val
    have hmat : g.val = matrixRows A := g.property.symm.trans (normalizeGrid_eq_matrixRows g.val)
    have hbound : ((stateEncoding basis).encode (step^[t] (initialState g.val))).length ≤
        p.eval ((gridEncoding basis).encode g.val).length := by
      rw [hmat]
      exact hp A (fun i j => skewEntry_swap g.val i.val j.val)
        (fun i => skewEntry_diag g.val i.val) t ht
    apply hbound.trans
    apply natPolynomial_monotone
    simp only [loopEncoding,BitEncoding.retract,BitEncoding.prod_length,
      stateEncoding,initialState]
    omega
  have hlo : FP (loopEncoding basis) (stateEncoding basis)
      (fun g : AlternatingGrid K => step^[g.val.length] (initialState g.val)) :=
    ⟨BoundedIterationMachine.computerOn (loopEncoding basis) (stateEncoding basis)
      step (fun g => g.val.length) (fun g => initialState g.val) (fun _ => rfl) body p hsize⟩
  have hout := (fp_snd (gridEncoding basis) (BitEncoding.nat.list.prod (numberFieldEncoding basis))).comp
    (fp_snd BitEncoding.nat.list (numberFieldEncoding basis))
  exact ((fp_prepareLoop basis).comp hlo).comp hout

/-- Unconditional complete encoded runtime theorem for arbitrary raw grids. -/
 theorem fp_evaluateGrid : FP (gridEncoding basis) (numberFieldEncoding basis) (evaluateGrid (K := K)) :=
  (fp_prepareGrid basis).comp (fp_evaluateAlternating basis)


include basis in
/-- The actual executable total evaluator equals the original literal signed
pairing sum on every square alternating matrix. -/
 theorem evaluateGrid_matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (hskew : ∀ i j, A j i = -A i j) (hdiag : ∀ i, A i i = 0) :
    evaluateGrid (matrixRows A) = MultiGraph.pairingPfaffian A := by
  rw [evaluateGrid_eq_elimination A hskew hdiag]
  exact MultiGraph.PfaffianElimination.evaluate_eq_pairingPfaffian A hskew hdiag

include basis in
 theorem matchingSum_eq_referenceSign_mul_evaluateGrid {n : ℕ} {E : Type*} [Fintype E]
    (G : MultiGraph (Fin n) E) (orientation : E → Bool)
    (ho : G.IsPfaffianOrientation orientation) (M₀ : Finset E)
    (hM₀ : G.PerfectMatching M₀) (w : E → K) :
    (∑ M : {M : Finset E // G.PerfectMatching M}, ∏ e ∈ M.val, w e) =
      G.matchingPfaffianSign orientation M₀ * evaluateGrid (matrixRows (G.occurrenceSkewMatrix orientation w)) := by
  rw [evaluateGrid_matrixRows basis _ (G.occurrenceSkewMatrix_swap orientation w)
    (G.occurrenceSkewMatrix_diag orientation w)]
  exact G.matchingSum_eq_referenceSign_mul_pairingPfaffian orientation ho M₀ hM₀ w


/-- One endpoint couples the literal executable algorithm, its encoded
polynomial runtime, and its original signed-Pfaffian semantics. -/
 theorem certified_evaluateGrid :
    FP (gridEncoding basis) (numberFieldEncoding basis) (evaluateGrid (K := K)) ∧
    ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) K),
      (∀ i j, A j i = -A i j) → (∀ i, A i i = 0) →
      evaluateGrid (matrixRows A) = MultiGraph.pairingPfaffian A :=
  ⟨fp_evaluateGrid basis,fun A hs hd => evaluateGrid_matrixRows basis A hs hd⟩

end PlanarHom.PfaffianList
