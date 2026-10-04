import PlanarHom.ClosedFamilyLocalGeometry

/-! The colored three-edge path is an actual outer-face gadget. Its signature
is H*K*H at unit background. Mixed gadget closure is the original section-four
operation rule, with the finite edge labels and geometric premise explicit. -/
noncomputable section
set_option maxHeartbeats 1000000
open scoped BigOperators
open Classical
open unitInterval
namespace PlanarHom.TwoTerminal
open MultiGraph

/-- Every edge occurrence has its own matrix; internal weights are counted once. -/
def coloredSignature {J E C R : Type} [Fintype J] [Fintype E] [Fintype C]
    [CommSemiring R] (G : TwoTerminal J E) (W : E → Matrix C C R) (w : C → R) :
    Matrix C C R := fun i j => ∑ coloring : J → C,
      (∏ v, w (coloring v)) * ∏ e, W e (extend i j coloring (G.src e)) (extend i j coloring (G.dst e))

@[simp] theorem coloredSignature_const {J E C R : Type} [Fintype J] [Fintype E]
    [Fintype C] [CommSemiring R] (G : TwoTerminal J E) (M : Matrix C C R) (w : C → R) :
    coloredSignature G (fun _ => M) w = signature G M w := rfl

def threeEdgePath : TwoTerminal Bool (Fin 3) where
  src := fun e => if e.val=0 then .inl false else if e.val=1 then .inr false else .inr true
  dst := fun e => if e.val=0 then .inr false else if e.val=1 then .inr true else .inl true

private def third : I := ⟨1/3, by norm_num⟩
private def twoThirds : I := ⟨2/3, by norm_num⟩
private def point : Bool ⊕ Bool → I × I
  | .inl false => (0,0)
  | .inl true => (1,0)
  | .inr false => (third,0)
  | .inr true => (twoThirds,0)

private def blend (a b t : I) : I :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ), by
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
      (mul_nonneg t.property.1 b.property.1), ?_⟩
    have h₁ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
    nlinarith⟩

private def curve (e : Fin 3) : C(I,I × I) where
  toFun t := (blend (point (threeEdgePath.src e)).1 (point (threeEdgePath.dst e)).1 t,0)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      change Continuous (fun t : I => (1-(t:ℝ))*_+(t:ℝ)*_)
      fun_prop
    · fun_prop

/-- Three consecutive horizontal segments, with their shared vertices retained. -/
def threeEdgePathStrip : StripDrawing threeEdgePath where
  point := point
  point_injective := by
    rintro (a|a) (b|b) h <;> cases a <;> cases b <;>
      norm_num [point, third, twoThirds, Prod.ext_iff, Subtype.ext_iff] at h
    all_goals rfl
  left := rfl
  right := rfl
  internal_inside := by intro b; cases b <;> norm_num [point, third, twoThirds, Inside]
  curve := curve
  curve_zero := by intro e; ext <;> simp [curve, blend, point]; fin_cases e <;> rfl
  curve_one := by intro e; ext <;> simp [curve, blend, point]; fin_cases e <;> rfl
  curve_inside := by
    intro e t ht
    rcases ht with ⟨ht₀,ht₁⟩
    have htpos : (0 : I) < t := ht₀
    have htlt : t < (1 : I) := ht₁
    fin_cases e <;> norm_num [curve, blend, point, threeEdgePath, third, twoThirds, Inside] <;>
      constructor <;> first | assumption | linarith
  interior_injective := by
    intro e f s t hs ht h
    have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
    rcases hs with ⟨hs₀,hs₁⟩
    rcases ht with ⟨ht₀,ht₁⟩
    fin_cases e <;> fin_cases f <;>
      norm_num [curve, blend, point, threeEdgePath, third, twoThirds] at hx ⊢
    all_goals first | (apply Subtype.ext; linarith) | linarith
  interior_avoids := by
    intro e t ht v h
    have hx := congrArg (fun p : I × I => (p.1 : ℝ)) h
    rcases ht with ⟨ht₀,ht₁⟩
    have hn0 : t ≠ (0 : I) := ne_of_gt (show (0 : I) < t from ht₀)
    have hn1 : t ≠ (1 : I) := ne_of_lt (show t < (1 : I) from ht₁)
    fin_cases e <;> rcases v with (b|b) <;> cases b <;>
      norm_num [curve, blend, point, threeEdgePath, third, twoThirds] at hx <;>
      first | exact hn0 hx | exact hn1 hx | linarith

theorem threeEdgePath_planarEdgeGadget : PlanarEdgeGadget threeEdgePath :=
  threeEdgePathStrip.planarEdgeGadget

/-- The middle and the two outside matrices are independent edge labels. -/
def seriesMatrices {C R : Type} (H K : Matrix C C R) : Fin 3 → Matrix C C R :=
  fun e => if e.val=1 then K else H

theorem coloredSignature_threeEdgePath {C R : Type} [Fintype C] [CommSemiring R]
    (H K : Matrix C C R) :
    coloredSignature threeEdgePath (seriesMatrices H K) (fun _ => 1) = H*K*H := by
  ext i j
  unfold coloredSignature
  rw [sum_colorings_bool]
  simp only [Finset.prod_const_one, one_mul]
  simp only [Matrix.mul_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp [threeEdgePath, seriesMatrices, extend, Fin.prod_univ_succ, mul_assoc]

end PlanarHom.TwoTerminal

namespace PlanarHom.ClosedMatrixFamily
variable {q : ℕ}

/-- The mixed version of the source's planar-gadget closure. Each occurrence
uses an existing matrix, and only Hermitian resulting signatures enter A. -/
structure MixedPlanarGadgetClosed (A : Set (Matrix (Fin q) (Fin q) ℝ)) : Prop where
  signature_mem : ∀ (J E : Type) [Fintype J] [Fintype E] (G : TwoTerminal J E),
    TwoTerminal.PlanarEdgeGadget G → ∀ W : E → Matrix (Fin q) (Fin q) ℝ,
    (∀ e, W e ∈ A) → (TwoTerminal.coloredSignature G W (fun _ => 1)).IsHermitian →
    TwoTerminal.coloredSignature G W (fun _ => 1) ∈ A

theorem MixedPlanarGadgetClosed.toPlanarGadgetClosed
    {A : Set (Matrix (Fin q) (Fin q) ℝ)} (h : MixedPlanarGadgetClosed A) : PlanarGadgetClosed A where
  signature_mem J E _ _ G hG H hH hsym := by
    simpa using h.signature_mem J E G hG (fun _ => H) (fun _ => hH) (by simpa using hsym)

/-- Genuine colored planar series composition, with unit internal weights. -/
theorem series_mem (A : Set (Matrix (Fin q) (Fin q) ℝ)) (h : MixedPlanarGadgetClosed A)
    (H K : Matrix (Fin q) (Fin q) ℝ) (hH : H ∈ A) (hK : K ∈ A)
    (hsH : H.IsHermitian) (hsK : K.IsHermitian) : H*K*H ∈ A := by
  rw [← TwoTerminal.coloredSignature_threeEdgePath]
  apply h.signature_mem Bool (Fin 3) TwoTerminal.threeEdgePath TwoTerminal.threeEdgePath_planarEdgeGadget
  · intro e
    simp only [TwoTerminal.seriesMatrices]
    split <;> assumption
  · rw [TwoTerminal.coloredSignature_threeEdgePath]
    rw [Matrix.IsHermitian, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      hsH.eq, hsK.eq, Matrix.mul_assoc]

end PlanarHom.ClosedMatrixFamily
