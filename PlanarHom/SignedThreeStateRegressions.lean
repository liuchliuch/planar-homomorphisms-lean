import PlanarHom.SignedThreeStateDichotomy
import PlanarHom.SignedThreeWeightPower

/-! Scope regressions for the signed cases that a nonnegative substitute
would miss. Every example is a checked instance of the literal criterion. -/
namespace PlanarHom.SignedThreeState

example : BooleanEasy (1:ℝ) 1 (-1) := by
  right; right; right
  norm_num

example : ¬((1:ℝ)*(-1)=1^2 ∨ (1:ℝ)=0 ∨ (1:ℝ)=(-1)) := by norm_num

example : ThreeStateEasy (blockMatrix (1:ℝ) 1 (-1) (-7)) := by
  right; left
  refine ⟨1,1,-1,-7,?_,Equiv.refl _,?_⟩
  · right; right; right; norm_num
  · intro i j; rfl

example : ThreeStateEasy (starMatrix (-2:ℝ) 3) := by
  right; right
  exact ⟨-2,3,Equiv.refl _,fun _ _=>rfl⟩

example : ThreeStateEasy (fun _ _ : Fin 3=>(-1:ℝ)) := by
  left
  have h : (fun _ _ : Fin 3=>(-1:ℝ))=Matrix.vecMulVec (fun _=> (-1:ℝ)) (fun _=>1) := by
    funext i j
    change (-1:ℝ)=(-1)*1
    ring
  rw [h]
  exact Matrix.rank_vecMulVec_le _ _

example : ¬BooleanEasy (1:ℝ) 2 (-1) := by norm_num [BooleanEasy]

example : (schurSquare (rankTwoChart (1:ℝ) 2 3 1 (-2))).det=(-8) := by
  rw [det_schurSquare_rankTwoChart]
  norm_num

end PlanarHom.SignedThreeState
