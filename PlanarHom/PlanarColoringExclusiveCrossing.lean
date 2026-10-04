import PlanarHom.PlanarEmbedding
import PlanarHom.ParsimoniousNorOneInThree
import Mathlib.Tactic.FinCases

/-! The literal five-vertex diamond (four-rim wheel) is a parsimonious
exclusive color crossover. This is Figure 11 of Barbanchon (TCS 319, 2004).
The plane drawing is constructed from explicit straight segments; planarity is
not assumed from the picture or from an abstract embedding certificate. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.PlanarColoringExclusiveCrossing
open MultiGraph
set_option maxHeartbeats 3000000

/-- Ports occur left, top, right, bottom; vertex 4 is the center. -/
def graph : MultiGraph (Fin 5) (Fin 8) where
  src := ![0,1,2,3,0,1,2,3]
  dst := ![1,2,3,0,4,4,4,4]

def point : Fin 5 → Plane := ![(-1,0),(0,1),(1,0),(0,-1),(0,0)]

def edgeCurve (e : Fin 8) : C(I,Plane) where
  toFun t := ((1-(t:ℝ))*(point (graph.src e)).1+(t:ℝ)*(point (graph.dst e)).1,
    (1-(t:ℝ))*(point (graph.src e)).2+(t:ℝ)*(point (graph.dst e)).2)
  continuous_toFun := by fun_prop

private theorem point_injective : Function.Injective point := by
  intro u v h
  fin_cases u <;> fin_cases v
  all_goals norm_num [point,Matrix.cons_val_two,Matrix.cons_val_three,Matrix.cons_val_four] at h
  all_goals rfl

private theorem curve_zero (e : Fin 8) : edgeCurve e 0=point (graph.src e) := by simp [edgeCurve]
private theorem curve_one (e : Fin 8) : edgeCurve e 1=point (graph.dst e) := by simp [edgeCurve]

private theorem interiors_disjoint (e f : Fin 8) (s t : I) (hs : Inside s) (ht : Inside t)
    (he : edgeCurve e s=edgeCurve f t) : e=f ∧ s=t := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  rcases hs with ⟨hs0,hs1⟩
  rcases ht with ⟨ht0,ht1⟩
  fin_cases e <;> fin_cases f
  all_goals dsimp [edgeCurve,graph,point] at hx hy
  all_goals norm_num at hx
  all_goals norm_num at hy
  all_goals norm_num
  all_goals try subst_vars
  all_goals try norm_num at hs0
  all_goals try norm_num at ht0
  all_goals try change (0:ℝ)<s.val at hs0
  all_goals try change (0:ℝ)<t.val at ht0
  all_goals first
    | rfl
    | assumption
    | (apply Subtype.ext; dsimp; linarith)
    | (exfalso; linarith)

private theorem interiors_avoid (e : Fin 8) (t : I) (ht : Inside t) (v : Fin 5) :
    edgeCurve e t≠point v := by
  intro he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  rcases ht with ⟨ht0,ht1⟩
  fin_cases e <;> fin_cases v
  all_goals dsimp [edgeCurve,graph,point] at hx hy
  all_goals norm_num at hx
  all_goals norm_num at hy
  all_goals first | (subst t; simp at ht0 ht1) | linarith

/-- A genuine continuous crossing-free drawing of every edge occurrence. -/
def drawing : PlaneDrawing graph where
  point := point
  point_injective := point_injective
  curve := edgeCurve
  curve_zero := curve_zero
  curve_one := curve_one
  interior_injective := interiors_disjoint
  interior_avoids := interiors_avoid

theorem planar : graph.Planar := ⟨drawing⟩

def Proper (col : Fin 5 → Fin 3) : Prop := ∀ e,col (graph.src e)≠col (graph.dst e)

def third (a b : Fin 3) : Fin 3 := 0-a-b

def extension (a b : Fin 3) : Fin 5 → Fin 3 := ![a,b,a,b,third a b]

/-- There are precisely six configurations, with one extension each. In
particular opposite ports agree, adjacent ports differ, and the center is forced. -/
theorem proper_iff (col : Fin 5 → Fin 3) :
    Proper col ↔ col 0≠col 1 ∧ col=extension (col 0) (col 1) := by
  have finite_check : ∀ a b c d z : Fin 3,
      (a≠b ∧ b≠c ∧ c≠d ∧ d≠a ∧ a≠z ∧ b≠z ∧ c≠z ∧ d≠z) ↔
        a≠b ∧ c=a ∧ d=b ∧ z=third a b := by decide
  have hproper : Proper col ↔
      col 0≠col 1 ∧ col 1≠col 2 ∧ col 2≠col 3 ∧ col 3≠col 0 ∧
      col 0≠col 4 ∧ col 1≠col 4 ∧ col 2≠col 4 ∧ col 3≠col 4 := by
    simp [Proper,graph,Fin.forall_fin_succ,Matrix.cons_val_succ]
  rw [hproper,finite_check]
  constructor
  · rintro ⟨h,h2,h3,h4⟩
    refine ⟨h,?_⟩
    funext v
    fin_cases v <;> simp [extension,h2,h3,h4]
  · rintro ⟨h,he⟩
    exact ⟨h,congrFun he 2,congrFun he 3,congrFun he 4⟩

theorem extension_proper (a b : Fin 3) (hab : a≠b) : Proper (extension a b) := by
  rw [proper_iff]
  exact ⟨hab,rfl⟩

/-- Fixed input colors have exactly one whole-gadget coloring iff distinct. -/
theorem unique_extension (a b : Fin 3) :
    (∃! col : Fin 5 → Fin 3, Proper col ∧ col 0=a ∧ col 1=b) ↔ a≠b := by
  constructor
  · rintro ⟨col,⟨h,ha,hb⟩,_⟩
    simpa [ha,hb] using (proper_iff col).mp h |>.1
  · intro hab
    refine ⟨extension a b,⟨extension_proper a b hab,rfl,rfl⟩,?_⟩
    intro col h
    simpa [h.2.1,h.2.2] using ((proper_iff col).mp h.1).2

def coloringEquiv : {col : Fin 5 → Fin 3 // Proper col} ≃ {p : Fin 3 × Fin 3 // p.1≠p.2} where
  toFun col := ⟨(col.val 0,col.val 1),((proper_iff col.val).mp col.property).1⟩
  invFun p := ⟨extension p.val.1 p.val.2,extension_proper _ _ p.property⟩
  left_inv col := by
    apply Subtype.ext
    exact ((proper_iff col.val).mp col.property).2.symm
  right_inv p := rfl

theorem coloring_count : Fintype.card {col : Fin 5 → Fin 3 // Proper col}=6 := by
  rw [Fintype.card_congr coloringEquiv]
  decide

end PlanarHom.PlanarColoringExclusiveCrossing
