import PlanarHom.PlanarFaces
import PlanarHom.ColoredGadgetReindex
import PlanarHom.SignedBooleanHardnessAlgebra

/-! The actual three-edge endpoint-leaf gadget: one source edge and one leaf
at each terminal. Its literal crossing-free drawing is cofacial. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open unitInterval
namespace PlanarHom.SignedThreeState
open MultiGraph TwoTerminal

def endpointLeaves : TwoTerminal Bool (Fin 3) where
  src := ![.inl false,.inl false,.inl true]
  dst := ![.inl true,.inr false,.inr true]

namespace LeafDrawing
private def half : I := ⟨1/2,by norm_num⟩
private def quarter : I := ⟨1/4,by norm_num⟩
private def threeQuarters : I := ⟨3/4,by norm_num⟩
private def point : Bool⊕Bool→I×I
  | .inl false => (0,0)
  | .inl true => (1,0)
  | .inr false => (quarter,half)
  | .inr true => (threeQuarters,half)
private def blend (a b t : I) : I :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ),by
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
      (mul_nonneg t.property.1 b.property.1),?_⟩
    have h₁:=mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
    have h₂:=mul_le_mul_of_nonneg_left b.property.2 t.property.1
    nlinarith⟩
private def curve (e : Fin 3) : C(I,I×I) where
  toFun t := (blend (point (endpointLeaves.src e)).1 (point (endpointLeaves.dst e)).1 t,
    blend (point (endpointLeaves.src e)).2 (point (endpointLeaves.dst e)).2 t)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;>
      change Continuous (fun t:I=>(1-(t:ℝ))*_+(t:ℝ)*_) <;> fun_prop

def strip : StripDrawing endpointLeaves where
  point := point
  point_injective := by
    rintro (a|a) (b|b) h <;> cases a <;> cases b <;>
      norm_num [point,half,quarter,threeQuarters,Prod.ext_iff,Subtype.ext_iff] at h
    all_goals rfl
  left := rfl
  right := rfl
  internal_inside := by intro b; cases b <;> norm_num [point,half,quarter,threeQuarters,Inside]
  curve := curve
  curve_zero := by intro e; ext <;> simp [curve,blend]
  curve_one := by intro e; ext <;> simp [curve,blend]
  curve_inside := by
    intro e t ht
    rcases ht with ⟨ht₀,ht₁⟩
    have htpos : (0:I)<t := ht₀
    have htlt : t<(1:I) := ht₁
    fin_cases e <;> norm_num [curve,blend,point,endpointLeaves,half,quarter,threeQuarters,Inside] <;>
      constructor <;> first | assumption | linarith
  interior_injective := by
    intro e f s t hs ht h
    have hx:=congrArg (fun p:I×I=>(p.1:ℝ)) h
    have hy:=congrArg (fun p:I×I=>(p.2:ℝ)) h
    rcases hs with ⟨hs₀,hs₁⟩
    rcases ht with ⟨ht₀,ht₁⟩
    fin_cases e <;> fin_cases f <;>
      norm_num [curve,blend,point,endpointLeaves,half,quarter,threeQuarters] at hx hy ⊢
    all_goals first | (apply Subtype.ext; linarith) | linarith | (subst t; norm_num at ht₀) | (subst s; norm_num at hs₀)
  interior_avoids := by
    intro e t ht v h
    have hx:=congrArg (fun p:I×I=>(p.1:ℝ)) h
    have hy:=congrArg (fun p:I×I=>(p.2:ℝ)) h
    rcases ht with ⟨ht₀,ht₁⟩
    have hn0:t≠(0:I):=ne_of_gt (show (0:I)<t from ht₀)
    have hn1:t≠(1:I):=ne_of_lt (show t<(1:I) from ht₁)
    fin_cases e <;> rcases v with (b|b) <;> cases b <;>
      norm_num [curve,blend,point,endpointLeaves,half,quarter,threeQuarters] at hx hy <;>
      first | exact hn0 hx | exact hn1 hx | linarith
end LeafDrawing

theorem endpointLeaves_planar : PlanarEdgeGadget endpointLeaves := LeafDrawing.strip.planarEdgeGadget

def endpointLeavesFin : TwoTerminal (Fin 2) (Fin 3) :=
  endpointLeaves.reindexInternal finTwoEquiv.symm (Equiv.refl _)

theorem endpointLeavesFin_planar : PlanarEdgeGadget endpointLeavesFin :=
  reindexInternal_planar endpointLeaves finTwoEquiv.symm (Equiv.refl _) endpointLeaves_planar

/-- Each private leaf is summed independently. -/
theorem endpointLeaves_signature {C R : Type} [Fintype C] [CommSemiring R]
    (M : Matrix C C R) (i j : C) :
    signature endpointLeaves M (fun _=>1) i j=
      (∑x,M i x)*M i j*(∑y,M j y) := by
  unfold signature
  rw [sum_colorings_bool]
  simp only [TwoTerminal.assignmentWeight,edgeWeight,endpointLeaves,extend,Fin.prod_univ_three]
  simp only [Finset.prod_const_one,one_mul,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,Sum.elim_inl,Sum.elim_inr,
    Bool.false_eq_true,cond_false,cond_true]
  simp only [Finset.sum_mul,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  ring

end PlanarHom.SignedThreeState
