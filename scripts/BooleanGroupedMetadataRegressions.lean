import PlanarHom.BooleanGroupedMetadataMachines

open PlanarHom PlanarHom.BooleanGroupedMetadataMachines
open PlanarHom.BooleanFieldTower

-- A genuine endpoint: no evaluator oracle, size/height premise, or supplied
-- list of spectral nodes is assumed.
example {K : Type} [Field K] [Algebra ℚ K] {dimension b : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) (c a w : Fin b → K)
    (d : Fin b → ℕ) (g0 : Fin b) :
    Complexity.FP inputEncoding (metadataEncoding basis b) (metadata c a w d g0) :=
  fp_metadata basis c a w d g0

-- Recovery accepts exactly the metadata and the literal positive answers.
example {K : Type} [Field K] [Algebra ℚ K] {dimension b : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K) :
    Complexity.FP ((metadataEncoding basis b).prod (Complexity.numberFieldEncoding basis).list)
      (BooleanGroupedTableRecoveryMachines.inputEncoding basis b) (attachAnswers (b := b)) :=
  fp_attachAnswers basis b

-- Zero source length still emits its unique bounded product and one target.
example {K : Type} [Field K] [Algebra ℚ K] {b : ℕ}
    (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) (q : ℚ) :
    (nodes c a w d g0 (0,q)).length = 1 ∧
      targets c a w d g0 (0,q) = [embed b 1] := by
  exact ⟨length_nodes_zero c a w d g0 q,
    targets_zero_count c a w d g0 (0,q) (by simp [counts])⟩

-- A retained class of multiplicity zero has just the identity target.
example {K : Type} [Field K] [Algebra ℚ K] {b : ℕ}
    (c a w : Fin b → K) (d : Fin b → ℕ) (g0 : Fin b) (p : Input)
    (hd : d g0 = 0) : targets c a w d g0 p = [embed b 1] :=
  targets_zero_count c a w d g0 p (by simp [counts, hd])

-- Out-of-range binary counts are clipped before any variable power.
example : clipped (fun _ : Fin 2 => 2) (3, (1/2 : ℚ)) [1000000, 1] = ![6,1] := by
  funext i
  fin_cases i <;> norm_num [clipped, counts, List.getD]

-- The raw box retains repeats from a class with zero multiplicity.
example :
    (nodes (fun _ : Fin 2 => (2 : ℚ)) (fun _ => 0) (fun _ => 0)
      ![1,0] 0 (1,0)).map Prod.fst = [1,1,0,0] := by
  norm_num [nodes, node, ExponentVectors.box, cap, clipped, counts, List.getD,
    Fin.sum_univ_two, List.range_succ, Function.comp_def]

-- Targets are ascending despite the descending box/range machine.
example (c a w : Fin 1 → ℚ) :
    targets c a w (fun _ => 2) 0 (1,0) =
      [target c a w (fun _ => 2) 0 ((1,0),0),
       target c a w (fun _ => 2) 0 ((1,0),1),
       target c a w (fun _ => 2) 0 ((1,0),2)] := by
  simp [targets, counts, List.range_succ]

-- Radicand padding and the empty dimension have no hidden nonemptiness case.
example (a w : Fin 0 → ℚ) (p : Input) : radicandList a w p = [] := by
  simp [radicandList]

example : radicandList (fun _ : Fin 1 => (3 : ℚ)) (fun _ => 4) (5, 1/2) = [13] := by
  norm_num [radicandList, BooleanFieldCollision.radicands,
    BooleanFieldCollision.extend, List.ofFn_succ]

example (a w : Fin 2 → ℚ) (p : Input) : (radicandList a w p).getD 100 0 = 0 := by
  rw [radicandList_getD]
  simp [BooleanFieldCollision.radicands, BooleanFieldCollision.extend]
