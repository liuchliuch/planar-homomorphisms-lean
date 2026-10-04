import PlanarHom.PlanarFaces
import PlanarHom.WheatstoneLog

/-! The actual five-edge Wheatstone gadget: exact signature and explicit
crossing-free straight-line drawing with both terminals on the outer face. -/
noncomputable section
set_option maxHeartbeats 4000000
open scoped BigOperators
open unitInterval
namespace PlanarHom.TwoTerminal
open MultiGraph

def wheatstone : TwoTerminal Bool (Fin 5) where
  src := fun e => if e.val=0 then .inl false else if e.val=1 then .inr false else
    if e.val=2 then .inl false else if e.val=3 then .inr true else .inr false
  dst := fun e => if e.val=0 then .inr false else if e.val=1 then .inl true else
    if e.val=2 then .inr true else if e.val=3 then .inl true else .inr true

private def half : I := ⟨1/2, by norm_num⟩
private def quarter : I := ⟨1/4, by norm_num⟩
private def threeQuarters : I := ⟨3/4, by norm_num⟩
private def point : Bool ⊕ Bool → I × I
  | .inl false => (0,0)
  | .inl true => (1,0)
  | .inr false => (half,threeQuarters)
  | .inr true => (half,quarter)

private def blend (a b t : I) : I :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ), by
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
      (mul_nonneg t.property.1 b.property.1), ?_⟩
    have h₁ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
    nlinarith⟩

private def curve (e : Fin 5) : C(I, I × I) where
  toFun t := (blend (point (wheatstone.src e)).1 (point (wheatstone.dst e)).1 t,
    blend (point (wheatstone.src e)).2 (point (wheatstone.dst e)).2 t)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;>
      change Continuous (fun t : I => (1-(t:ℝ))*_+(t:ℝ)*_) <;> fun_prop

/-- The five straight segments meet only at their specified common endpoints. -/
def wheatstoneStrip : StripDrawing wheatstone where
  point := point
  point_injective := by
    rintro (a|a) (b|b) h <;> cases a <;> cases b <;>
      norm_num [point, half, quarter, threeQuarters, Prod.ext_iff, Subtype.ext_iff] at h
    all_goals rfl
  left := rfl
  right := rfl
  internal_inside := by intro b; cases b <;> norm_num [point, half, Inside]
  curve := curve
  curve_zero := by intro e; ext <;> simp [curve, blend]
  curve_one := by intro e; ext <;> simp [curve, blend]
  curve_inside := by
    intro e t ht
    rcases ht with ⟨ht₀,ht₁⟩
    have htpos : (0 : I) < t := ht₀
    have htlt : t < (1 : I) := ht₁
    fin_cases e <;> norm_num [curve, blend, point, wheatstone, half, Inside] <;> constructor <;> first | assumption | linarith
  interior_injective := by
    intro e f s t hs ht h
    have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
    have hy := congrArg (fun p : I × I => (p.2 : ℝ)) h
    rcases hs with ⟨hs₀,hs₁⟩
    rcases ht with ⟨ht₀,ht₁⟩
    fin_cases e <;> fin_cases f <;>
      norm_num [curve, blend, point, wheatstone, half, quarter, threeQuarters] at hx hy ⊢
    all_goals first | (apply Subtype.ext; linarith) | linarith
  interior_avoids := by
    intro e t ht v h
    have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
    have hy := congrArg (fun p : I × I => (p.2 : ℝ)) h
    rcases ht with ⟨ht₀,ht₁⟩
    have hn0 : t ≠ (0 : I) := ne_of_gt (show (0 : I) < t from ht₀)
    have hn1 : t ≠ (1 : I) := ne_of_lt (show t < (1 : I) from ht₁)
    fin_cases e <;> rcases v with (b|b) <;> cases b <;>
      norm_num [curve, blend, point, wheatstone, half, quarter, threeQuarters] at hx hy <;> first | exact hn0 hx | exact hn1 hx | linarith

theorem wheatstone_planarEdgeGadget : PlanarEdgeGadget wheatstone := wheatstoneStrip.planarEdgeGadget

/-- The signature has exactly the five edge factors shown in Figure1; internal
vertices are summed, and terminal background weights are absent. -/
theorem signature_wheatstone {C R : Type} [Fintype C] [CommSemiring R]
    (M : Matrix C C R) (i j : C) :
    signature wheatstone M (fun _ => 1) i j = ∑ a : C, ∑ b : C,
      M i a * M a j * M i b * M b j * M a b := by
  unfold signature
  rw [sum_colorings_bool]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [assignmentWeight, edgeWeight, wheatstone, extend, Fin.prod_univ_succ]
  ac_rfl

theorem signature_wheatstone_distanceKernel {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (x : ℝ) :
    signature wheatstone (EntropyCompletion.distanceKernel G x) (fun _ => 1) =
      WheatstoneCoefficients.wheatstoneMatrix G x := by
  ext i j
  rw [signature_wheatstone, WheatstoneCoefficients.wheatstoneMatrix_apply]

end PlanarHom.TwoTerminal
