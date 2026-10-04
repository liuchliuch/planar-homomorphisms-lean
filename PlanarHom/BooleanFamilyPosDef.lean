import PlanarHom.BooleanLoopNormalization
import PlanarHom.BooleanLogPositivity

/-! Genuine positive definiteness of the rational-parameter tensor family in
(5.2), throughout0<x<1, from a direct completed-square identity. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanFamilyPosDef
open BooleanPDNormalization Matrix

theorem normalForm_posDef (θ u : ℝ) (hθ : 0<θ) (hu : u^2<1) : (normalForm θ u).PosDef := by
  have hn : θ≠0 := ne_of_gt hθ
  refine ⟨?_,?_⟩
  · ext i j
    cases i <;> cases j <;> simp [normalForm,Matrix.conjTranspose_apply]
  · intro v hv
    have he : star v ⬝ᵥ ((normalForm θ u) *ᵥ v)=
        θ*(v false+(u/θ)*v true)^2+((1-u^2)/θ)*(v true)^2 := by
      simp only [dotProduct,Matrix.mulVec,Fintype.sum_bool,Pi.star_apply,star_trivial,normalForm,
        Bool.false_eq_true,Bool.true_eq_false,↓reduceIte]
      field_simp
      ring
    rw [he]
    have hc : 0<(1-u^2)/θ := div_pos (sub_pos.mpr hu) hθ
    have hfirst : 0≤θ*(v false+(u/θ)*v true)^2 := mul_nonneg hθ.le (sq_nonneg _)
    by_cases ht:v true=0
    · have hf : v false≠0 := by
        intro hf
        apply hv
        funext i
        cases i <;> simp [hf,ht]
      simpa only [ht,mul_zero,add_zero,zero_pow (by decide : 2≠0)] using
        mul_pos hθ (sq_pos_of_ne_zero hf)
    · exact add_pos_of_nonneg_of_pos hfirst (mul_pos hc (sq_pos_of_ne_zero ht))

theorem normalForm_entry_pos (θ u : ℝ) (hθ : 0<θ) (hu : 0<u) :
    ∀i j,0<normalForm θ u i j := by
  intro i j
  cases i <;> cases j <;> simp [normalForm,hθ,hu,inv_pos.mpr hθ]

theorem parameterFactor_posDef (θ w x : ℝ) (hθ : 0<θ) (hw : 0<w) (hw1 : w<1)
    (hx : 0<x) (hx1 : x<1) (t : ℕ) : (normalForm (θ^t) (w*x)).PosDef := by
  apply normalForm_posDef _ _ (pow_pos hθ t)
  have hmul : 0<w*x := mul_pos hw hx
  have hlt : w*x<1 := lt_trans (by simpa using mul_lt_mul_of_pos_left hx1 hw) hw1
  nlinarith

theorem parameterTensor_posDef {ι : Type} [Fintype ι] [DecidableEq ι]
    (θ w : ι→ℝ) (hθ : ∀r,0<θ r) (hw : ∀r,0<w r) (hw1 : ∀r,w r<1)
    (x : ℝ) (hx : 0<x) (hx1 : x<1) (t : ℕ) :
    (CubeTensorExponential.tensor (fun r=>normalForm ((θ r)^t) (w r*x))).PosDef := by
  exact BooleanLogPositivity.tensor_posDef _ (fun r=>parameterFactor_posDef _ _ _ (hθ r) (hw r) (hw1 r) hx hx1 t)

theorem parameterTensor_entry_pos {ι : Type} [Fintype ι]
    (θ w : ι→ℝ) (hθ : ∀r,0<θ r) (hw : ∀r,0<w r)
    (x : ℝ) (hx : 0<x) (t : ℕ) :
    ∀z z',0<CubeTensorExponential.tensor (fun r=>normalForm ((θ r)^t) (w r*x)) z z' := by
  intro z z'
  exact Finset.prod_pos (fun r _=>normalForm_entry_pos _ _ (pow_pos (hθ r) t) (mul_pos (hw r) hx) _ _)

end PlanarHom.BooleanFamilyPosDef
