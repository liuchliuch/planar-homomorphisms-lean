import PlanarHom.RoutingCellTrace

/-! Explicit polynomial occurrence bounds for every routing compiler input,
including off-promise inputs; no source numeric validity is needed for growth. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree AdjacentRailRouting

@[simp] theorem swapLayer_rails_length (i m : ℕ) (rs : List ℕ) : (swapLayer m i rs).rails.length=rs.length := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs => cases rs <;> simp [swapLayer,passive,wireRails_length]
  | succ i ih => cases rs <;> simp [swapLayer,passive,wireRails_length,ih]

theorem copyLayer_rails_length_le (i m : ℕ) (rs : List ℕ) : (copyLayer m i rs).rails.length≤rs.length+1 := by
  induction i generalizing m rs with
  | zero => cases rs <;> simp [copyLayer,passive,wireRails_length]
  | succ i ih =>
    cases rs with
    | nil => simp [copyLayer,passive,wireRails]
    | cons a rs => simpa [copyLayer] using Nat.add_le_add_right (ih (m+6) rs) 1

@[simp] theorem sweep_rails_length (is : List ℕ) (m : ℕ) (rs : List ℕ) :
    (sweep m rs is).rails.length=rs.length := by
  induction is generalizing m rs with
  | nil => rfl
  | cons i is ih => simp [sweep,LayerResult.then,ih]

theorem sweep_instructions_length (is : List ℕ) (m : ℕ) (rs : List ℕ) :
    (sweep m rs is).instructions.length≤ is.length*rs.length := by
  induction is generalizing m rs with
  | nil => simp [sweep,LayerResult.identity]
  | cons i is ih =>
    have hfirst := swapLayer_instructions_length i m rs
    have htail := ih (swapLayer m i rs).variableCount (swapLayer m i rs).rails
    simp only [swapLayer_rails_length] at htail
    simp only [sweep,LayerResult.then,List.length_append,List.length_cons]
    nlinarith

theorem copyMacro_rails_length_le (n i m : ℕ) (rs : List ℕ) :
    (copyMacro n i m rs).rails.length≤rs.length+1 := by
  unfold copyMacro
  split
  · simp only [LayerResult.then,sweep_rails_length]
    exact (copyLayer_rails_length_le _ _ _).trans_eq (by simp)
  · simp [LayerResult.identity]

theorem copyMacro_instructions_length (n i m : ℕ) (rs : List ℕ) :
    (copyMacro n i m rs).instructions.length≤(rs.length+1)*copyColumns n i := by
  by_cases hi : i<n
  · let is := moveScript i (n-1-i)
    let first := sweep m rs is
    let second := copyLayer first.variableCount (n-1) first.rails
    have hfirst := sweep_instructions_length is m rs
    have hsecond := copyLayer_instructions_length (n-1) first.variableCount first.rails
    have hthird := sweep_instructions_length is.reverse second.variableCount second.rails
    have hlfirst : first.rails.length=rs.length := sweep_rails_length is m rs
    have hlsecond : second.rails.length≤rs.length+1 := by
      simpa only [hlfirst] using copyLayer_rails_length_le (n-1) first.variableCount first.rails
    have hbound := Nat.mul_le_mul_left is.length hlsecond
    simp only [List.length_reverse] at hthird
    simp only [copyMacro,if_pos hi,LayerResult.then,List.length_append,copyColumns]
    change first.instructions.length+(second.instructions.length+
      (sweep second.variableCount second.rails is.reverse).instructions.length)≤_
    have his : is.length=n-1-i := moveScript_length _ _
    nlinarith
  · simp [copyMacro,copyColumns,hi,LayerResult.identity]

theorem gatherMacro_rails_length_le (is : List ℕ) (n m : ℕ) (rs : List ℕ) :
    (gatherMacro n m rs is).rails.length≤rs.length+is.length := by
  induction is generalizing m rs with
  | nil => simp [gatherMacro,LayerResult.identity]
  | cons i is ih =>
    have hfirst := copyMacro_rails_length_le n i m rs
    have htail := ih (copyMacro n i m rs).variableCount (copyMacro n i m rs).rails
    simp only [gatherMacro,LayerResult.then,List.length_cons]
    omega

theorem gatherMacro_instructions_length (is : List ℕ) (n m : ℕ) (rs : List ℕ) :
    (gatherMacro n m rs is).instructions.length≤(rs.length+is.length)*gatherColumns n is := by
  induction is generalizing m rs with
  | nil => simp [gatherMacro,LayerResult.identity,gatherColumns]
  | cons i is ih =>
    let first := copyMacro n i m rs
    have hfirst := copyMacro_instructions_length n i m rs
    have hsize : first.rails.length≤rs.length+1 := copyMacro_rails_length_le n i m rs
    have htail := ih first.variableCount first.rails
    have hmul := Nat.mul_le_mul_right (gatherColumns n is)
      (show first.rails.length+is.length≤rs.length+(is.length+1) by omega)
    have hmul' := Nat.mul_le_mul_right (copyColumns n i)
      (show rs.length+1≤rs.length+(is.length+1) by omega)
    simp only [gatherMacro,LayerResult.then,List.length_append]
    change first.instructions.length+(gatherMacro n first.variableCount first.rails is).instructions.length≤_
    simp only [List.length_cons,gatherColumns,List.map_cons,List.sum_cons]
    change first.instructions.length+(gatherMacro n first.variableCount first.rails is).instructions.length≤
      (rs.length+(is.length+1))*(copyColumns n i+gatherColumns n is)
    nlinarith

@[simp] theorem checkLayer_instructions_length (n m : ℕ) (rs : List ℕ) :
    (checkLayer n m rs).instructions.length=(rs.take n).length+1 := by
  simp [checkLayer,wireProgram]

theorem clauseLayer_rails_length_le (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) :
    (clauseLayer n m rs c).rails.length≤n := by
  simp [clauseLayer,LayerResult.then,checkLayer,wireRails_length,List.length_take]

theorem clauseLayer_instructions_length (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : rs.length≤n) :
    (clauseLayer n m rs c).instructions.length≤(n+3)*clauseColumns n c := by
  have hg := gatherMacro_instructions_length [c.1,c.2.1,c.2.2] n m rs
  have hn : (List.take n (gatherClause n m rs c).rails).length≤n := List.length_take_le _ _
  have hmul := Nat.mul_le_mul_right (gatherColumns n [c.1,c.2.1,c.2.2])
    (show rs.length+3≤n+3 by omega)
  simp only [List.length_cons,List.length_nil] at hg
  simp only [clauseLayer,LayerResult.then,List.length_append]
  change (gatherClause n m rs c).instructions.length+
    (checkLayer n (gatherClause n m rs c).variableCount (gatherClause n m rs c).rails).instructions.length≤_
  rw [checkLayer_instructions_length]
  unfold clauseColumns
  change (gatherClause n m rs c).instructions.length≤_ at hg
  nlinarith

theorem formulaLayers_instructions_length (f : Formula ℕ) (n m : ℕ) (rs : List ℕ) (hr : rs.length≤n) :
    (formulaLayers n m rs f).instructions.length≤(n+3)*formulaColumns n f := by
  induction f generalizing m rs with
  | nil => simp [formulaLayers,LayerResult.identity,formulaColumns]
  | cons c cs ih =>
    have hfirst := clauseLayer_instructions_length n m rs c hr
    have htail := ih (clauseLayer n m rs c).variableCount (clauseLayer n m rs c).rails
      (clauseLayer_rails_length_le n m rs c)
    simp only [formulaLayers,LayerResult.then,List.length_append]
    change (clauseLayer n m rs c).instructions.length+
      (formulaLayers n (clauseLayer n m rs c).variableCount (clauseLayer n m rs c).rails cs).instructions.length≤_
    simp only [formulaColumns,List.map_cons,List.sum_cons]
    change _≤(n+3)*(clauseColumns n c+formulaColumns n cs)
    nlinarith

end PlanarHom.PositiveBlockProgram

namespace PlanarHom.PositiveRoutingCompiler
open PositiveBlockProgram ParsimoniousNorOneInThree

theorem program_length (f : NumericFormula) :
    (program f).length≤(f.1+3)*f.2.length*(6*f.1+4) := by
  have h := formulaLayers_instructions_length f.2 f.1 f.1 (List.range f.1) (by simp)
  have hm := Nat.mul_le_mul_left (f.1+3) (formulaColumns_le f.1 f.2)
  change (program f).length≤_ at h
  nlinarith

theorem compile_variables_bound (f : NumericFormula) :
    (compile f).1≤f.1+15*((f.1+3)*f.2.length*(6*f.1+4)) := by
  exact (width_bound f.1 (program f)).trans (by have h := program_length f; nlinarith)

end PlanarHom.PositiveRoutingCompiler
