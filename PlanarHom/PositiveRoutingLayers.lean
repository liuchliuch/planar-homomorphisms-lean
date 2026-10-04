import PlanarHom.PositiveWireBatch
import PlanarHom.AdjacentRailRouting

/-! Literal numeric routing layers. Passive wires are explicitly materialized,
so layer ports are genuinely distinct fresh variableCount at the next grid line. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open CountingCookLevin ParsimoniousBlockTemplate AdjacentRailRouting

structure LayerResult where
  variableCount : ℕ
  rails : List ℕ
  instructions : List Instruction

/-- A complete layer of straight identity wires. -/
def passive (m : ℕ) (rails : List ℕ) : LayerResult :=
  ⟨m+6*rails.length,wireRails m rails,wireProgram rails⟩

/-- A single adjacent crossing, with every other rail carried by an actual
six-fresh-variable equality block. An invalid pair becomes a passive layer. -/
def swapLayer : ℕ → ℕ → List ℕ → LayerResult
  | m,0,a::b::rs =>
    let tail := passive (m+15) rs
    ⟨tail.variableCount,m::(m+1)::tail.rails,crossing a b::tail.instructions⟩
  | m,i+1,a::rs =>
    let tail := swapLayer (m+6) i rs
    ⟨tail.variableCount,m::tail.rails,wire a::tail.instructions⟩
  | m,_,rs => passive m rs

/-- One input is fanned out to two fresh ports; the original upper port is
listed first. All lower passive rails move into the next free row. -/
def copyLayer : ℕ → ℕ → List ℕ → LayerResult
  | m,0,a::rs =>
    let tail := passive (m+12) rs
    ⟨tail.variableCount,(m+1)::m::tail.rails,fan a::tail.instructions⟩
  | m,i+1,a::rs =>
    let tail := copyLayer (m+6) i rs
    ⟨tail.variableCount,m::tail.rails,wire a::tail.instructions⟩
  | m,_,[] => passive m []

@[simp] theorem crossing_output_upper (xs : List Bool) (a b : ℕ) :
    readBit (step xs (crossing a b)) xs.length=readBit xs b := by
  simp [step,crossing,refs,Kind.template,Template.auxiliary,crossover,PositiveCrossoverDrawing.completion,
    readBit,List.getElem?_append_right,List.ofFn_succ,Fin.natAdd,Fin.castAdd,Fin.castLE]

@[simp] theorem crossing_output_lower (xs : List Bool) (a b : ℕ) :
    readBit (step xs (crossing a b)) (xs.length+1)=readBit xs a := by
  simp [step,crossing,refs,Kind.template,Template.auxiliary,crossover,PositiveCrossoverDrawing.completion,
    readBit,List.getElem?_append_right,List.ofFn_succ,Fin.natAdd,Fin.castAdd,Fin.castLE]

@[simp] theorem fan_output_upper (xs : List Bool) (a : ℕ) :
    readBit (step xs (fan a)) (xs.length+1)=readBit xs a := by
  simp [step,fan,refs,Kind.template,Template.auxiliary,fanout,PositiveFanoutDrawing.completion,
    readBit,List.getElem?_append_right,List.ofFn_succ,Fin.natAdd,Fin.castAdd,Fin.castLE]

@[simp] theorem fan_output_lower (xs : List Bool) (a : ℕ) :
    readBit (step xs (fan a)) xs.length=readBit xs a := by
  simp [step,fan,refs,Kind.template,Template.auxiliary,fanout,PositiveFanoutDrawing.completion,
    readBit,List.getElem?_append_right,List.ofFn_succ,Fin.natAdd,Fin.castAdd,Fin.castLE]

private theorem old_rails_step (xs : List Bool) (rs : List ℕ) (op : Instruction)
    (hr : ∀r∈rs,r<xs.length) : rs.map (readBit (step xs op))=rs.map (readBit xs) := by
  apply List.map_congr_left
  intro r h
  exact step_read_old xs op r (hr r h)

/-- The materialized swap layer implements the exact adjacent-list operation. -/
theorem swapLayer_values (i : ℕ) (rs : List ℕ) (xs : List Bool) (hr : ∀r∈rs,r<xs.length) :
    (swapLayer xs.length i rs).rails.map (readBit (execute (swapLayer xs.length i rs).instructions xs))=
      swapAt i (rs.map (readBit xs)) := by
  induction i generalizing rs xs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      cases rs with
      | nil => exact wireRails_values [a] xs hr
      | cons b rs =>
        let ys := step xs (crossing a b)
        have hys : ys.length=xs.length+15 := by simp [ys,crossing,Kind.template,crossover]
        have hr' : ∀r∈rs,r<ys.length := fun r h => (hr r (by simp [h])).trans_le (by omega)
        have ht := wireRails_values rs ys hr'
        have ho := old_rails_step xs rs (crossing a b) (fun r h => hr r (by simp [h]))
        rw [ho,hys] at ht
        change readBit (execute (wireProgram rs) ys) xs.length::
          readBit (execute (wireProgram rs) ys) (xs.length+1)::
          (wireRails (xs.length+15) rs).map (readBit (execute (wireProgram rs) ys))=
          readBit xs b::readBit xs a::rs.map (readBit xs)
        rw [ht,execute_read_old _ _ _ (by omega),execute_read_old _ _ _ (by omega)]
        simp [ys]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      let ys := step xs (wire a)
      have hys : ys.length=xs.length+6 := by simp [ys,wire,Kind.template,equality]
      have hr' : ∀r∈rs,r<ys.length := fun r h => (hr r (by simp [h])).trans_le (by omega)
      have ht := ih rs ys hr'
      have ho := old_rails_step xs rs (wire a) (fun r h => hr r (by simp [h]))
      rw [ho,hys] at ht
      change readBit (execute (swapLayer (xs.length+6) i rs).instructions ys) xs.length::
        (swapLayer (xs.length+6) i rs).rails.map (readBit (execute (swapLayer (xs.length+6) i rs).instructions ys))=
        readBit xs a::swapAt i (rs.map (readBit xs))
      rw [ht,execute_read_old _ _ _ (by omega)]
      simp [ys]

/-- The materialized fanout layer implements exact adjacent duplication. -/
theorem copyLayer_values (i : ℕ) (rs : List ℕ) (xs : List Bool) (hr : ∀r∈rs,r<xs.length) :
    (copyLayer xs.length i rs).rails.map (readBit (execute (copyLayer xs.length i rs).instructions xs))=
      duplicateAt i (rs.map (readBit xs)) := by
  induction i generalizing rs xs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      let ys := step xs (fan a)
      have hys : ys.length=xs.length+12 := by simp [ys,fan,Kind.template,fanout]
      have hr' : ∀r∈rs,r<ys.length := fun r h => (hr r (by simp [h])).trans_le (by omega)
      have ht := wireRails_values rs ys hr'
      have ho := old_rails_step xs rs (fan a) (fun r h => hr r (by simp [h]))
      rw [ho,hys] at ht
      change readBit (execute (wireProgram rs) ys) (xs.length+1)::
        readBit (execute (wireProgram rs) ys) xs.length::
        (wireRails (xs.length+12) rs).map (readBit (execute (wireProgram rs) ys))=
        readBit xs a::readBit xs a::rs.map (readBit xs)
      rw [ht,execute_read_old _ _ _ (by omega),execute_read_old _ _ _ (by omega)]
      simp [ys]
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      let ys := step xs (wire a)
      have hys : ys.length=xs.length+6 := by simp [ys,wire,Kind.template,equality]
      have hr' : ∀r∈rs,r<ys.length := fun r h => (hr r (by simp [h])).trans_le (by omega)
      have ht := ih rs ys hr'
      have ho := old_rails_step xs rs (wire a) (fun r h => hr r (by simp [h]))
      rw [ho,hys] at ht
      change readBit (execute (copyLayer (xs.length+6) i rs).instructions ys) xs.length::
        (copyLayer (xs.length+6) i rs).rails.map (readBit (execute (copyLayer (xs.length+6) i rs).instructions ys))=
        readBit xs a::duplicateAt i (rs.map (readBit xs))
      rw [ht,execute_read_old _ _ _ (by omega)]
      simp [ys]

end PlanarHom.PositiveBlockProgram
