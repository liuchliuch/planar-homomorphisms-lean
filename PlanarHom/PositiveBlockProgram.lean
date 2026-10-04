import PlanarHom.BlockTemplateMachines

/-! Numeric acyclic programs of the four physically drawn positive-clause
blocks. Every primitive is serialized as a finite tag and three binary inputs;
all fresh variables and the complete emitted clause list are materialized. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open Complexity ParsimoniousNorOneInThree CountingCookLevin ParsimoniousBlockTemplate

inductive Kind | wire | cross | fan | test deriving DecidableEq, Fintype

def Kind.template : Kind → Template
  | .wire => equality
  | .cross => crossover
  | .fan => fanout
  | .test => termination

theorem Kind.inputs_le (k : Kind) : k.template.inputs≤3 := by cases k <;> decide

abbrev Instruction := Kind × (ℕ × ℕ × ℕ)

def refs (op : Instruction) (i : Fin op.1.template.inputs) : ℕ :=
  ![op.2.1,op.2.2.1,op.2.2.2] ⟨i.val,lt_of_lt_of_le i.isLt op.1.inputs_le⟩

def width (m : ℕ) : List Instruction → ℕ
  | [] => m
  | op::ops => width (m+op.1.template.fresh) ops

def Valid (m : ℕ) : List Instruction → Prop
  | [] => True
  | op::ops => (∀ i,refs op i<m) ∧ Valid (m+op.1.template.fresh) ops

def network (m : ℕ) : List Instruction → Formula ℕ
  | [] => []
  | op::ops => op.1.template.emit m (refs op)++network (m+op.1.template.fresh) ops

def step (xs : List Bool) (op : Instruction) : List Bool :=
  xs++List.ofFn (op.1.template.auxiliary (fun i => readBit xs (refs op i)))

def execute (ops : List Instruction) (xs : List Bool) : List Bool := ops.foldl step xs

def Accepts : List Instruction → List Bool → Prop
  | [],_ => True
  | op::ops,xs => op.1.template.accepts (fun i => readBit xs (refs op i)) ∧ Accepts ops (step xs op)

@[simp] theorem step_length (xs : List Bool) (op : Instruction) :
    (step xs op).length=xs.length+op.1.template.fresh := by simp [step]

@[simp] theorem execute_length (ops : List Instruction) (xs : List Bool) :
    (execute ops xs).length=width xs.length ops := by
  induction ops generalizing xs with
  | nil => rfl
  | cons op ops ih =>
    change (execute ops (step xs op)).length=_
    rw [ih,step_length]
    rfl

theorem width_mono (m n : ℕ) (ops : List Instruction) (hm : m≤n) : width m ops≤width n ops := by
  induction ops generalizing m n with
  | nil => exact hm
  | cons op ops ih => exact ih _ _ (by omega)

theorem width_ge (m : ℕ) (ops : List Instruction) : m≤width m ops := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih =>
    have h := ih (m+op.1.template.fresh)
    change m≤width (m+op.1.template.fresh) ops
    omega

theorem execute_take (ops : List Instruction) (xs : List Bool) (n : ℕ) (hn : n≤xs.length) :
    (execute ops xs).take n=xs.take n := by
  induction ops generalizing xs with
  | nil => rfl
  | cons op ops ih =>
    change (execute ops (step xs op)).take n=_
    rw [ih _ (by simp; omega)]
    simp [step,List.take_append_of_le_length hn]

theorem execute_read_old (ops : List Instruction) (xs : List Bool) (i : ℕ) (hi : i<xs.length) :
    readBit (execute ops xs) i=readBit xs i := by
  have h := execute_take ops xs (i+1) (by omega)
  have hr := congrArg (fun zs => readBit zs i) h
  dsimp only at hr
  rw [readBit_take (execute ops xs) (i+1) i (by omega),readBit_take xs (i+1) i (by omega)] at hr
  exact hr

/-- Full emitted block sequence is equivalent to its accepting deterministic
store extension, retaining literal output arrays and every auxiliary bit. -/
theorem network_iff (ops : List Instruction) (xs : List Bool) (m : ℕ)
    (hvalid : Valid m ops) (hm : width m ops≤xs.length) :
    Satisfies (network m ops) (readBit xs) ↔
      Accepts ops (xs.take m) ∧ xs.take (width m ops)=execute ops (xs.take m) := by
  induction ops generalizing m with
  | nil => simp [network,Satisfies,Accepts,width,execute]
  | cons op ops ih =>
    obtain ⟨href,hrest⟩ := hvalid
    have hnext : m+op.1.template.fresh≤xs.length := (width_ge _ ops).trans hm
    have hold : (fun i => readBit xs (refs op i))=(fun i => readBit (xs.take m) (refs op i)) := by
      funext i
      exact (readBit_take xs m (refs op i) (href i)).symm
    rw [network,satisfies_append,Template.emit_correct _ xs m (refs op) hnext,hold,
      ih (m+op.1.template.fresh) hrest hm]
    have hstep : step (xs.take m) op=
        xs.take m++List.ofFn (op.1.template.auxiliary (fun i => readBit (xs.take m) (refs op i))) := rfl
    rw [←hstep]
    change (_ ∧ _) ∧ (_ ∧ _) ↔
      (_ ∧ Accepts ops (step (xs.take m) op)) ∧
      xs.take (width (m+op.1.template.fresh) ops)=execute ops (step (xs.take m) op)
    constructor
    · rintro ⟨⟨ha,he⟩,hb,hf⟩
      exact ⟨⟨ha,by simpa [he] using hb⟩,by simpa [he] using hf⟩
    · rintro ⟨⟨ha,hb⟩,hf⟩
      have he := congrArg (fun zs : List Bool => zs.take (m+op.1.template.fresh)) hf
      have hslen : (step (xs.take m) op).length=m+op.1.template.fresh := by
        simp [List.length_take_of_le (show m≤xs.length by omega)]
      dsimp only at he
      rw [List.take_take,Nat.min_eq_left (width_ge _ ops),
        execute_take ops (step (xs.take m) op) (m+op.1.template.fresh) hslen.ge,
        List.take_of_length_le (l := step (xs.take m) op) hslen.le] at he
      exact ⟨⟨ha,he⟩,by simpa [he] using hb,by simpa [he] using hf⟩

/-- Compiled coordinates stay below the final materialized variable header. -/
theorem network_valid (ops : List Instruction) (m : ℕ) (hv : Valid m ops) :
    NumericValid (width m ops,network m ops) := by
  induction ops generalizing m with
  | nil => intro c hc; simp [network] at hc
  | cons op ops ih =>
    obtain ⟨href,hr⟩ := hv
    intro c hc
    rw [network] at hc
    rcases List.mem_append.mp hc with hc | hc
    · have h := op.1.template.emit_valid m (refs op) href c hc
      have hw := width_ge (m+op.1.template.fresh) ops
      change c.1<width (m+op.1.template.fresh) ops ∧
        c.2.1<width (m+op.1.template.fresh) ops ∧ c.2.2<width (m+op.1.template.fresh) ops
      omega
    · exact ih (m+op.1.template.fresh) hr c hc

end PlanarHom.PositiveBlockProgram
