import PlanarHom.BooleanEigenvalueBranches

open PlanarHom.BooleanEigenvalueBranches

example : (cParameter 2 3)^2-(aParameter 2 3)^2=1 := parameter_identity 2 3 (by norm_num)
example : aParameter 1 7=0 := by simp
example : 0<aParameter 2 7 := aParameter_pos (by norm_num) (by norm_num)
example : bParameter 2 1 1=(3/4 : ℝ)^2 := by norm_num [bParameter,aParameter]

-- The logarithmic derivative is proved inside the negative-y continuation
-- interval, not merely on the original positive parameter interval.
example : HasDerivAt (logRatio (5/4) (3/4) (1/2)) (-10/21) (-5/4) := by
  have hs : Real.sqrt (4 : ℝ)=2 := (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  convert hasDerivAt_logRatio (5/4) (3/4) (1/2) (-5/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) using 1 <;>
    norm_num [root,Real.sqrt_div,hs]

example : 0<ratio (5/4) (3/4) (1/2) (-5/4) ∧ ratio (5/4) (3/4) (1/2) (-5/4)<1 :=
  (branches_positive (5/4) (3/4) (1/2) (-5/4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)).2.2

example {θ : ℝ} {t : ℕ} (hθ : 1≤θ) (ht : 0<t) : aParameter θ t≠0 ↔ 1<θ :=
  aParameter_ne_zero_iff hθ ht

#print axioms hasDerivAt_logRatio
#print axioms parameter_identity
#print axioms aParameter_ne_zero_iff
