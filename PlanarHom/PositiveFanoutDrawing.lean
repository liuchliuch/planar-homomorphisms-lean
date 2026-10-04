import PlanarHom.PositiveEqualityDrawing
import PlanarHom.ParsimoniousNorNumericNetwork

/-! A three-corner positive-one-in-three fanout. One free input is copied to two
independent output ports, with exactly one extension and an actual drawing. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveFanoutDrawing
open MultiGraph ParsimoniousNorOneInThree IntegerStraightDrawing
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

def upper : Fin 7 → Fin 13 := ![0,1,3,4,5,6,7]
def lower : Fin 7 → Fin 13 := ![0,2,8,9,10,11,12]
def formula : Formula (Fin 13) :=
  rename upper PositiveEqualityDrawing.formula++rename lower PositiveEqualityDrawing.formula

def clauses : Fin 10 → Clause (Fin 13) := ![
  (0,3,4),(1,3,4),(5,6,4),(5,7,4),(6,5,7),
  (0,8,9),(2,8,9),(10,11,9),(10,12,9),(11,10,12)]

theorem formula_eq : formula=List.ofFn clauses := by decide

def occurrence (c : Fin 10) : Fin 3 → Fin 13 := ![(clauses c).1,(clauses c).2.1,(clauses c).2.2]
def incidence : MultiGraph (Fin 13 ⊕ Fin 10) (Fin 10 × Fin 3) where
  src e := .inl (occurrence e.1 e.2)
  dst e := .inr e.1

/-- Input 0 is lower left; outputs 1 and 2 are upper and lower right. -/
def variablePoint : Fin 13 → Point := ![
  (0,0),(64,64),(64,0),
  (32,34),(32,40),(32,44),(24,36),(40,52),
  (32,2),(32,8),(32,12),(24,12),(40,12)]
def clausePoint : Fin 10 → Point := ![
  (16,20),(48,52),(24,34),(40,50),(32,46),
  (16,4),(48,4),(24,10),(40,10),(32,14)]
def point : Fin 13 ⊕ Fin 10 → Point := Sum.elim variablePoint clausePoint

def certificate : Certificate incidence point where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawing : PlaneDrawing incidence := IntegerStraightDrawing.drawing certificate

def completion (x : Bool) : Fin 13 → Bool :=
  ![x,x,x,!x,false,true,false,false,!x,false,true,false,false]

/-- Every variable in both local equality circuits is forced by the input. -/
theorem satisfies_eq_completion (a : Fin 13 → Bool) : Satisfies formula a ↔ a=completion (a 0) := by
  rw [formula,satisfies_append,satisfies_rename,satisfies_rename,
    PositiveEqualityDrawing.satisfies_eq_completion,PositiveEqualityDrawing.satisfies_eq_completion]
  constructor
  · rintro ⟨hu,hl⟩
    funext v
    fin_cases v
    · rfl
    all_goals first
      | exact congrFun hu 1
      | exact congrFun hu 2
      | exact congrFun hu 3
      | exact congrFun hu 4
      | exact congrFun hu 5
      | exact congrFun hu 6
      | exact congrFun hl 1
      | exact congrFun hl 2
      | exact congrFun hl 3
      | exact congrFun hl 4
      | exact congrFun hl 5
      | exact congrFun hl 6
  · intro h
    have hu : completion (a 0) ∘ upper=PositiveEqualityDrawing.completion (a 0) := by
      funext v; fin_cases v <;> rfl
    have hl : completion (a 0) ∘ lower=PositiveEqualityDrawing.completion (a 0) := by
      funext v; fin_cases v <;> rfl
    exact ⟨by simpa only [←h] using hu,by simpa only [←h] using hl⟩

@[simp] theorem completion_satisfies (x : Bool) : Satisfies formula (completion x) :=
  (satisfies_eq_completion _).mpr rfl

def solutionsEquiv (x : Bool) : {a : Fin 13 → Bool // Satisfies formula a ∧ a 0=x} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨completion x,completion_satisfies x,rfl⟩
  left_inv a := by
    apply Subtype.ext
    exact ((satisfies_eq_completion a.val).mp a.property.1).trans (by rw [a.property.2]) |>.symm
  right_inv _ := rfl

theorem count_one (x : Bool) : Fintype.card {a : Fin 13 → Bool // Satisfies formula a ∧ a 0=x}=1 :=
  (Fintype.card_congr (solutionsEquiv x)).trans (by simp)

/-- Boundary and interior positions are explicit integer facts for routing. -/
theorem inner_points : ∀ v : Fin 13 ⊕ Fin 10,
    v≠.inl 0 → v≠.inl 1 → v≠.inl 2 →
      0<(point v).1 ∧ (point v).1<64 ∧ 0<(point v).2 ∧ (point v).2<64 := by decide

end PlanarHom.PositiveFanoutDrawing
