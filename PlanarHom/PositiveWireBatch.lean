import PlanarHom.PositiveBlockProgramCounting

/-! Materialized passive wires for complete routing layers. Every passive rail
is copied into fresh named output variables; no geometric wire is implicit. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree CountingCookLevin ParsimoniousBlockTemplate

def wire (x : ℕ) : Instruction := (.wire,(x,0,0))
def crossing (upper lower : ℕ) : Instruction := (.cross,(lower,upper,0))
def fan (x : ℕ) : Instruction := (.fan,(x,0,0))
def test (x y z : ℕ) : Instruction := (.test,(x,y,z))

def wireProgram (rails : List ℕ) : List Instruction := rails.map wire

def wireRails (m : ℕ) : List ℕ → List ℕ
  | [] => []
  | _::rs => m::wireRails (m+6) rs

@[simp] theorem execute_append (ops more : List Instruction) (xs : List Bool) :
    execute (ops++more) xs=execute more (execute ops xs) := List.foldl_append

theorem accepts_append (ops more : List Instruction) (xs : List Bool) :
    Accepts (ops++more) xs ↔ Accepts ops xs ∧ Accepts more (execute ops xs) := by
  induction ops generalizing xs with
  | nil => simp [Accepts,execute]
  | cons op ops ih =>
    change (_ ∧ Accepts (ops++more) (step xs op)) ↔ _
    rw [ih]
    simp only [Accepts,execute,List.foldl_cons,and_assoc]

@[simp] theorem wireRails_length (m : ℕ) (rails : List ℕ) : (wireRails m rails).length=rails.length := by
  induction rails generalizing m with
  | nil => rfl
  | cons a rails ih => simp [wireRails,ih]

@[simp] theorem wire_width (m : ℕ) (rails : List ℕ) : width m (wireProgram rails)=m+6*rails.length := by
  induction rails generalizing m with
  | nil => simp [wireProgram,width]
  | cons a rails ih =>
    change width (m+6) (wireProgram rails)=_
    rw [ih]
    simp only [List.length_cons]
    omega

theorem wireRails_bounds (m : ℕ) (rails : List ℕ) (r : ℕ) (hr : r∈wireRails m rails) :
    m≤r ∧ r<m+6*rails.length := by
  induction rails generalizing m with
  | nil => simp [wireRails] at hr
  | cons a rails ih =>
    simp only [wireRails,List.mem_cons] at hr
    rcases hr with rfl | hr
    · simp only [List.length_cons]; omega
    · have h := ih (m+6) hr
      simp only [List.length_cons]
      omega

theorem wireProgram_valid (m : ℕ) (rails : List ℕ) (hr : ∀ r∈rails,r<m) : Valid m (wireProgram rails) := by
  induction rails generalizing m with
  | nil => trivial
  | cons a rails ih =>
    refine ⟨?_,ih (m+6) (fun r h => (hr r (by simp [h])).trans_le (by omega))⟩
    intro i
    change Fin 1 at i
    fin_cases i
    exact hr a (by simp)

@[simp] theorem wireProgram_accepts (rails : List ℕ) (xs : List Bool) : Accepts (wireProgram rails) xs := by
  induction rails generalizing xs with
  | nil => trivial
  | cons a rails ih => exact ⟨trivial,ih _⟩

theorem step_read_old (xs : List Bool) (op : Instruction) (i : ℕ) (hi : i<xs.length) :
    readBit (step xs op) i=readBit xs i := by
  simp only [step,readBit,List.getElem?_append_left hi]

@[simp] theorem wire_output (xs : List Bool) (x : ℕ) :
    readBit (step xs (wire x)) xs.length=readBit xs x := by
  simp [step,wire,refs,Kind.template,Template.auxiliary,equality,PositiveEqualityDrawing.completion,
    readBit,List.getElem?_append_right,List.ofFn_succ,Fin.natAdd,Fin.castAdd,Fin.castLE]

/-- Every emitted passive output carries exactly its original rail value. -/
theorem wireRails_values (rails : List ℕ) (xs : List Bool) (hr : ∀ r∈rails,r<xs.length) :
    (wireRails xs.length rails).map (readBit (execute (wireProgram rails) xs))=rails.map (readBit xs) := by
  induction rails generalizing xs with
  | nil => rfl
  | cons a rails ih =>
    let ys := step xs (wire a)
    have hys : ys.length=xs.length+6 := by simp [ys,wire,Kind.template,equality]
    have hr' : ∀ r∈rails,r<ys.length := fun r h => (hr r (by simp [h])).trans_le (by omega)
    have ht := ih ys hr'
    have he : rails.map (readBit ys)=rails.map (readBit xs) := by
      apply List.map_congr_left
      intro r h
      exact step_read_old xs (wire a) r (hr r (by simp [h]))
    rw [he,hys] at ht
    change readBit (execute (wireProgram rails) ys) xs.length::
        (wireRails (xs.length+6) rails).map (readBit (execute (wireProgram rails) ys))=
      readBit xs a::rails.map (readBit xs)
    rw [ht,execute_read_old _ _ _ (by omega)]
    exact congrArg (fun b => b::rails.map (readBit xs)) (wire_output xs a)

end PlanarHom.PositiveBlockProgram
