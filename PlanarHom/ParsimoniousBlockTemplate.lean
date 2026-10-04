import PlanarHom.NorExactOneSemantics
import PlanarHom.PositiveEqualityDrawing
import PlanarHom.PositiveCrossoverBox
import PlanarHom.PositiveFanoutDrawing

/-! Uniform numerical realization of a checked local Boolean template. Its
auxiliaries are contiguous fresh materialized variables, and the full list
prefix theorem proves uniqueness rather than only existential satisfiability. -/
noncomputable section
open Classical
namespace PlanarHom.ParsimoniousBlockTemplate
open ParsimoniousNorOneInThree CountingCookLevin Complexity

structure Template where
  inputs : ℕ
  fresh : ℕ
  clauses : Formula (Fin (inputs+fresh))
  accepts : (Fin inputs → Bool) → Prop
  extend : (Fin inputs → Bool) → Fin (inputs+fresh) → Bool
  old_value : ∀ a i,extend a (Fin.castAdd fresh i)=a i
  correct : ∀ a,Satisfies clauses a ↔
    accepts (fun i => a (Fin.castAdd fresh i)) ∧ a=extend (fun i => a (Fin.castAdd fresh i))

namespace Template

def auxiliary (T : Template) (a : Fin T.inputs → Bool) : Fin T.fresh → Bool :=
  fun i => T.extend a (Fin.natAdd T.inputs i)

def translate (T : Template) (m : ℕ) (refs : Fin T.inputs → ℕ) (v : Fin (T.inputs+T.fresh)) : ℕ :=
  if h : v.val<T.inputs then refs ⟨v.val,h⟩ else m+(v.val-T.inputs)

@[simp] theorem translate_old (T : Template) (m : ℕ) (refs : Fin T.inputs → ℕ) (i : Fin T.inputs) :
    T.translate m refs (Fin.castAdd T.fresh i)=refs i := by simp [translate]
@[simp] theorem translate_fresh (T : Template) (m : ℕ) (refs : Fin T.inputs → ℕ) (i : Fin T.fresh) :
    T.translate m refs (Fin.natAdd T.inputs i)=m+i.val := by simp [translate]

def emit (T : Template) (m : ℕ) (refs : Fin T.inputs → ℕ) : Formula ℕ :=
  rename (T.translate m refs) T.clauses

/-- General local uniqueness exposed only on the actually fresh variables. -/
theorem correct_auxiliary (T : Template) (a : Fin (T.inputs+T.fresh) → Bool) :
    Satisfies T.clauses a ↔
      T.accepts (fun i => a (Fin.castAdd T.fresh i)) ∧
      (fun i => a (Fin.natAdd T.inputs i))=T.auxiliary (fun i => a (Fin.castAdd T.fresh i)) := by
  rw [T.correct]
  constructor
  · rintro ⟨ha,he⟩
    exact ⟨ha,congrArg (fun f i => f (Fin.natAdd T.inputs i)) he⟩
  · rintro ⟨ha,he⟩
    refine ⟨ha,?_⟩
    funext i
    refine Fin.addCases ?_ ?_ i
    · intro j
      exact (T.old_value (fun i => a (Fin.castAdd T.fresh i)) j).symm
    · intro j
      exact congrFun he j

/-- The compiled numerical block has exactly the checked Boolean meaning. -/
theorem emit_correct (T : Template) (xs : List Bool) (m : ℕ) (refs : Fin T.inputs → ℕ)
    (hm : m+T.fresh≤xs.length) :
    Satisfies (T.emit m refs) (readBit xs) ↔
      T.accepts (fun i => readBit xs (refs i)) ∧
      xs.take (m+T.fresh)=xs.take m++List.ofFn (T.auxiliary (fun i => readBit xs (refs i))) := by
  rw [emit,satisfies_rename,T.correct_auxiliary]
  have hold : (fun i => (readBit xs ∘ T.translate m refs) (Fin.castAdd T.fresh i))=
      (fun i => readBit xs (refs i)) := by funext i; simp
  rw [hold]
  have hfresh : (fun i => (readBit xs ∘ T.translate m refs) (Fin.natAdd T.inputs i))=
      (fun i => readBit xs (m+i.val)) := by funext i; simp
  rw [hfresh]
  have hp := NorExactOne.prefix_append_iff xs
    (List.ofFn (T.auxiliary (fun i => readBit xs (refs i)))) m (by simpa using hm)
  simp only [List.length_ofFn] at hp
  rw [hp]
  constructor
  · rintro ⟨ha,he⟩
    refine ⟨ha,?_⟩
    intro i
    have hi : i.val<T.fresh := by simpa using i.isLt
    simpa [readBit,hi] using congrFun he ⟨i.val,hi⟩
  · rintro ⟨ha,he⟩
    refine ⟨ha,?_⟩
    funext i
    simpa [readBit] using he ⟨i.val,by simpa using i.isLt⟩

/-- Valid inputs and contiguous freshness imply every emitted coordinate is
within the new explicit variable count. -/
theorem emit_valid (T : Template) (m : ℕ) (refs : Fin T.inputs → ℕ)
    (hrefs : ∀ i,refs i<m) : NumericValid (m+T.fresh,T.emit m refs) := by
  intro c hc
  obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hc
  have hbound (v : Fin (T.inputs+T.fresh)) : T.translate m refs v<m+T.fresh := by
    unfold translate
    split
    · exact (hrefs _).trans_le (by omega)
    · omega
  exact ⟨hbound d.1,hbound d.2.1,hbound d.2.2⟩

end Template

/-- Literal equality wire: one input and six uniquely forced fresh variables. -/
def equality : Template where
  inputs := 1
  fresh := 6
  clauses := PositiveEqualityDrawing.formula
  accepts _ := True
  extend a := PositiveEqualityDrawing.completion (a 0)
  old_value a i := by fin_cases i; rfl
  correct a := by
    rw [PositiveEqualityDrawing.satisfies_eq_completion]
    simp only [true_and]
    rfl

/-- Literal crossover: two inputs and fifteen uniquely forced fresh variables. -/
def crossover : Template where
  inputs := 2
  fresh := 15
  clauses := PositiveCrossoverDrawing.formula
  accepts _ := True
  extend a := PositiveCrossoverDrawing.completion (a 0) (a 1)
  old_value a i := by fin_cases i <;> rfl
  correct a := by
    rw [PositiveCrossoverDrawing.satisfies_eq_completion]
    simp only [true_and]
    rfl

/-- Literal fanout: one input and twelve uniquely forced fresh variables. -/
def fanout : Template where
  inputs := 1
  fresh := 12
  clauses := PositiveFanoutDrawing.formula
  accepts _ := True
  extend a := PositiveFanoutDrawing.completion (a 0)
  old_value a i := by fin_cases i; rfl
  correct a := by
    rw [PositiveFanoutDrawing.satisfies_eq_completion]
    simp only [true_and]
    rfl

/-- Clause termination has no fresh variables and tests the three actual rails. -/
def termination : Template where
  inputs := 3
  fresh := 0
  clauses := [(0,1,2)]
  accepts a := ExactlyOne (a 0) (a 1) (a 2)
  extend a := a
  old_value a i := rfl
  correct a := by simp [Satisfies]

end PlanarHom.ParsimoniousBlockTemplate
