import PlanarHom.IntegerStraightDrawing
import PlanarHom.ParsimoniousBooleanProgram

/-! A literal uniquely extending equality wire with a checked plane incidence
drawing. Grounding is local; there is no globally shared constant wire. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveEqualityDrawing
open MultiGraph ParsimoniousNorOneInThree IntegerStraightDrawing
set_option maxRecDepth 50000
set_option maxHeartbeats 4000000

/-- 0 and 1 are terminals; 2 is their complement; 3,5,6 are false; 4 is true. -/
def clauses : Fin 5 → Clause (Fin 7) := ![(0,2,3),(1,2,3),(4,5,3),(4,6,3),(5,4,6)]
def formula : Formula (Fin 7) := List.ofFn clauses

def occurrence (c : Fin 5) : Fin 3 → Fin 7 := ![(clauses c).1,(clauses c).2.1,(clauses c).2.2]
def incidence : MultiGraph (Fin 7 ⊕ Fin 5) (Fin 5 × Fin 3) where
  src e := .inl (occurrence e.1 e.2)
  dst e := .inr e.1

def variablePoint : Fin 7 → Point := ![(0,0),(16,0),(8,2),(8,8),(8,12),(6,12),(10,12)]
def clausePoint : Fin 5 → Point := ![(4,4),(12,4),(6,10),(10,10),(8,14)]
def point : Fin 7 ⊕ Fin 5 → Point := Sum.elim variablePoint clausePoint

def certificate : Certificate incidence point where
  injective := by decide
  nondegenerate := by decide
  separated := by decide
  avoids := by decide

def drawing : PlaneDrawing incidence := IntegerStraightDrawing.drawing certificate

def completion (x : Bool) : Fin 7 → Bool := ![x,x,!x,false,true,false,false]

private theorem equality_local (x y a : Bool) :
    ExactlyOne x a false ∧ ExactlyOne y a false ↔ y=x ∧ a= !x := by
  cases x <;> cases y <;> cases a <;> simp [ExactlyOne]

/-- The terminal equality and every local auxiliary value are forced. -/
theorem satisfies_iff (a : Fin 7 → Bool) :
    Satisfies formula a ↔ a 1=a 0 ∧ a 2= !a 0 ∧ a 3=false ∧ a 4=true ∧ a 5=false ∧ a 6=false := by
  have hs : Satisfies formula a ↔
      ExactlyOne (a 0) (a 2) (a 3) ∧ ExactlyOne (a 1) (a 2) (a 3) ∧
      (ExactlyOne (a 4) (a 5) (a 3) ∧ ExactlyOne (a 4) (a 6) (a 3) ∧ ExactlyOne (a 5) (a 4) (a 6)) := by
    simp [Satisfies,formula,clauses,List.ofFn_succ]
  rw [hs,forceTrue_local]
  constructor
  · rintro ⟨h0,h1,ht,hf,hi,hk⟩
    rw [hf] at h0 h1
    have h := (equality_local (a 0) (a 1) (a 2)).mp ⟨h0,h1⟩
    exact ⟨h.1,h.2,hf,ht,hi,hk⟩
  · rintro ⟨hy,ha,hf,ht,hi,hk⟩
    have h := (equality_local (a 0) (a 1) (a 2)).mpr ⟨hy,ha⟩
    exact ⟨by simpa [hf] using h.1,by simpa [hf] using h.2,ht,hf,hi,hk⟩

theorem satisfies_eq_completion (a : Fin 7 → Bool) : Satisfies formula a ↔ a=completion (a 0) := by
  rw [satisfies_iff]
  constructor
  · rintro ⟨h1,h2,h3,h4,h5,h6⟩
    funext v
    fin_cases v <;> first | rfl | assumption
  · intro h
    exact ⟨congrFun h 1,congrFun h 2,congrFun h 3,congrFun h 4,congrFun h 5,congrFun h 6⟩

@[simp] theorem completion_satisfies (x : Bool) : Satisfies formula (completion x) :=
  (satisfies_eq_completion _).mpr rfl

def solutionsEquiv (x : Bool) : {a : Fin 7 → Bool // Satisfies formula a ∧ a 0=x} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨completion x,completion_satisfies x,rfl⟩
  left_inv a := by
    apply Subtype.ext
    exact ((satisfies_eq_completion a.val).mp a.property.1).trans (by rw [a.property.2]) |>.symm
  right_inv _ := rfl

theorem count_one (x : Bool) : Fintype.card {a : Fin 7 → Bool // Satisfies formula a ∧ a 0=x}=1 :=
  (Fintype.card_congr (solutionsEquiv x)).trans (by simp)

end PlanarHom.PositiveEqualityDrawing
