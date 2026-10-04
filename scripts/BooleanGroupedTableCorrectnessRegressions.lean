import PlanarHom.BooleanGroupedTableCorrectness

noncomputable section
open scoped BigOperators
namespace PlanarHom.BooleanGroupedTableCorrectnessRegressions
open BooleanFieldTower BooleanFieldTowerAlgebra BooleanFieldTowerConvolutionMachines
open BooleanGroupedGridRecoveryMachines BooleanGroupedGridRecoverySemantics
open BooleanGroupedTableRecoveryMachines BooleanGroupedTableRecoverySemantics
open BooleanGroupedTableCorrectness

private def ns : List (Node ℚ 0) := [(0,2),(0,2),(1,3)]
private def ts : List (Tower ℚ 0) := [5,7]
private theorem labels : ∀ q ∈ ns, q.1 < ts.length := by
  simp [ns, ts]
private theorem nonzero : ∀ q ∈ ns, norm (radicands ([] : List ℚ)) 0 q.2 ≠ 0 := by
  norm_num [ns, norm]
private theorem cross : ∀ q ∈ ns, ∀ r ∈ ns, q.1 ≠ r.1 →
    norm (radicands ([] : List ℚ)) 0 (sub 0 q.2 r.2) ≠ 0 := by
  norm_num [ns, norm, sub, add, neg]

/-- The inside list really retains both copies of the repeated node. -/
example : (makeRow 0 (ns,((5 : ℚ),0))).2.1 = [2,2] := by
  decide

/-- The actual machine inserts zero before all other outsider nodes. -/
example : (makeRow 0 (ns,((5 : ℚ),0))).2.2 = [0,3] := by
  decide

example : ∀ r ∈ rows 0 (ns,ts), RowValid 0 [] r :=
  rows_valid 0 [] ns ts nonzero cross

/-- Identical stored roots at the same label both interpolate correctly. -/
example : (tablePolynomial 0 [] ns ts).eval (ofTower (radicands []) 0 (2 : ℚ)) =
    ofTower (radicands []) 0 (5 : ℚ) := by
  exact tablePolynomial_eval 0 [] ns ts labels nonzero cross (0,2) (by simp [ns])

example : (tablePolynomial 0 [] ns ts).coeff 0 = 0 :=
  tablePolynomial_zero 0 [] ns ts

private def node : Bool → Fin ns.length := fun b => if b then ⟨2,by decide⟩ else ⟨0,by decide⟩
private def weight : Bool → Carrier (radicands ([] : List ℚ)) 0 := fun b => if b then 3 else -2
private def moment (h : Fin (degreeCap ns.length)) : ℚ :=
  (-2)*2^(h.val+1) + 3*3^(h.val+1)

private theorem moment_correct (h : Fin (degreeCap ns.length)) :
    algebraMap ℚ (Carrier (radicands ([] : List ℚ)) 0) (moment h) =
    ∑ a : Bool, weight a * (ofTower (radicands []) 0 (ns[(node a).val].2))^(h.val+1) := by
  simp [moment, node, weight, ns, ofTower, algebraMap_eq, embed, mul, neg]
  ring

/-- Signed weights recover their weighted target from strictly positive moments
through the actual grid/coefficient machine. -/
example : BooleanGroupedTableRecoveryMachines.recover 0
    ([],(ns,(ts,List.ofFn moment))) = (11 : ℚ) := by
  apply recover_eq_of_weighted_targets_embed 0 [] ns ts labels nonzero cross
    node weight (List.ofFn moment) (by simp only [List.length_ofFn])
  · intro h
    simpa only [List.getElem_ofFn] using moment_correct h
  · norm_num [node, weight, ns, ts, ofTower, embed, mul, neg, Fintype.sum_bool]

/-- No target rows is legal, including its automatically inserted zero moment. -/
example : tablePolynomial 0 ([] : List ℚ) [] [] = 0 := rfl

example : ∀ r ∈ rows 0 (([] : List (Node ℚ 0)),[]), RowValid 0 [] r := by
  simp [rows]

/-- An empty group still has a valid inserted zero outsider. -/
example : RowValid 0 ([] : List ℚ) (makeRow 0 ([],((5 : ℚ),0))) := by
  apply makeRow_valid <;> simp

/-- Empty assignments and node lists recover zero even with a nonempty target
list; the generated rows remain meaningful and total. -/
example : BooleanGroupedTableRecoveryMachines.recover 0
    (([] : List ℚ),([],([5],List.ofFn (fun _ : Fin (degreeCap 0) => (0 : ℚ))))) = 0 := by
  apply recover_eq_of_weighted_targets_embed (A := Fin 0) 0 [] [] [5]
    (by simp) (by simp) (by simp) (fun a => a.elim0)
    (fun a => a.elim0) _ (by simp only [List.length_ofFn, List.length_nil])
  · intro h
    simp only [List.getElem_ofFn, _root_.map_zero, Fin.sum_univ_zero]
  · rfl

/-- The tower may have zero divisors: specializing the radical to a square does
not add a field hypothesis to the same-label repeated-node theorem. -/
example : (tablePolynomial 1 ([1] : List ℚ)
    [(0,embed 1 2),(0,embed 1 2)] [embed 1 5]).eval
    (ofTower (radicands [1]) 1 (embed 1 2)) = ofTower (radicands [1]) 1 (embed 1 5) := by
  apply tablePolynomial_eval 1 [1] [(0,embed 1 2),(0,embed 1 2)] [embed 1 5]
    (by simp) ?_ (by simp) (0,embed 1 2) (by simp)
  intro q hq
  simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hq
  subst q
  norm_num [norm, embed, mul, sub, add, neg, zero]

end PlanarHom.BooleanGroupedTableCorrectnessRegressions
