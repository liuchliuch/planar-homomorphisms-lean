import PlanarHom.PositiveCrossoverDrawing
import PlanarHom.GridBoxAssembly

/-! The exact logical crossover packaged as a literal four-port square for the
proved global grid assembler, with its explicit unique Boolean completion. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveCrossoverDrawing
open MultiGraph ParsimoniousNorOneInThree GridBoxAssembly

abbrev Inner := Fin 13 ⊕ Fin 12

def vertexEquiv : (Fin 4 ⊕ Inner) ≃ (Fin 17 ⊕ Fin 12) :=
  (Equiv.sumAssoc (Fin 4) (Fin 13) (Fin 12)).symm.trans
    (Equiv.sumCongr finSumFinEquiv (Equiv.refl (Fin 12)))

def boxGraph : MultiGraph (Fin 4 ⊕ Inner) (Fin 12 × Fin 3) where
  src e := vertexEquiv.symm (incidence.src e)
  dst e := vertexEquiv.symm (incidence.dst e)

def relabeledDrawing : PlaneDrawing boxGraph where
  point := drawing.point ∘ vertexEquiv
  point_injective := drawing.point_injective.comp vertexEquiv.injective
  curve := drawing.curve
  curve_zero e := by simp [boxGraph,drawing.curve_zero]
  curve_one e := by simp [boxGraph,drawing.curve_one]
  interior_injective := drawing.interior_injective
  interior_avoids e t ht v := drawing.interior_avoids e t ht (vertexEquiv v)

/-- Concrete constructor consumed by the actual global square gluing theorem. -/
def boxDrawing : BoxDrawing boxGraph where
  drawing := relabeledDrawing
  ports k := by
    fin_cases k <;> norm_num [relabeledDrawing,vertexEquiv,drawing,IntegerStraightDrawing.drawing,
      point,variablePoint,IntegerStraightDrawing.toPlane,lattice,corner,finSumFinEquiv,Fin.castAdd,Fin.castLE,
      Matrix.cons_val_two,Matrix.cons_val_three]
  internal w := by
    have hi : ∀ w : Inner,0<(point (vertexEquiv (.inr w))).1 ∧ (point (vertexEquiv (.inr w))).1<16 ∧
        0<(point (vertexEquiv (.inr w))).2 ∧ (point (vertexEquiv (.inr w))).2<16 := by decide
    change 0<((point (vertexEquiv (.inr w))).1:ℝ) ∧ ((point (vertexEquiv (.inr w))).1:ℝ)<16 ∧
      0<((point (vertexEquiv (.inr w))).2:ℝ) ∧ ((point (vertexEquiv (.inr w))).2:ℝ)<16
    exact_mod_cast hi w
  curves := curves_inside

def completion (x y : Bool) : Fin 17 → Bool := ![
  x,y,x,y,decide (x=y),
  !(x||y),!x&&y,x&&!y,
  !(y||x),!y&&x,y&&!x,
  !(x||y),!x&&y,x&&!y,
  !(y||x),!y&&x,y&&!x]

/-- Full assignment uniqueness, rather than just a boundary relation. -/
theorem satisfies_eq_completion (a : Fin 17 → Bool) :
    Satisfies formula a ↔ a=completion (a 0) (a 1) := by
  rw [satisfies_iff]
  constructor
  · rintro ⟨h2,h3,h4,ha⟩
    funext v
    fin_cases v
    · rfl
    · rfl
    · exact h2
    · exact h3
    · exact h4
    all_goals first
      | exact congrFun (congrFun ha 0) 0
      | exact congrFun (congrFun ha 0) 1
      | exact congrFun (congrFun ha 0) 2
      | exact congrFun (congrFun ha 1) 0
      | exact congrFun (congrFun ha 1) 1
      | exact congrFun (congrFun ha 1) 2
      | exact congrFun (congrFun ha 2) 0
      | exact congrFun (congrFun ha 2) 1
      | exact congrFun (congrFun ha 2) 2
      | exact congrFun (congrFun ha 3) 0
      | exact congrFun (congrFun ha 3) 1
      | exact congrFun (congrFun ha 3) 2
  · intro h
    have he : (fun k j => completion (a 0) (a 1) (auxiliaryIndex k j))=crossoverAuxiliary (a 0) (a 1) := by
      funext k j
      fin_cases k <;> fin_cases j <;> rfl
    exact ⟨congrFun h 2,congrFun h 3,congrFun h 4,by simpa only [←h] using he⟩

@[simp] theorem completion_satisfies (x y : Bool) : Satisfies formula (completion x y) :=
  (satisfies_eq_completion _).mpr rfl

/-- Every fixed input pair has exactly one satisfying full local assignment. -/
def solutionsEquiv (x y : Bool) :
    {a : Fin 17 → Bool // Satisfies formula a ∧ a 0=x ∧ a 1=y} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨completion x y,⟨completion_satisfies x y,rfl,rfl⟩⟩
  left_inv a := by
    apply Subtype.ext
    exact ((satisfies_eq_completion a.val).mp a.property.1).trans (by rw [a.property.2.1,a.property.2.2]) |>.symm
  right_inv _ := rfl

theorem count_one (x y : Bool) :
    Fintype.card {a : Fin 17 → Bool // Satisfies formula a ∧ a 0=x ∧ a 1=y}=1 :=
  (Fintype.card_congr (solutionsEquiv x y)).trans (by simp)

end PlanarHom.PositiveCrossoverDrawing
