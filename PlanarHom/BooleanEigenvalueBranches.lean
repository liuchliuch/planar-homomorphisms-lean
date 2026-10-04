import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! Actual positive eigenvalue branches for Section5.1, with exact logarithmic
ratio derivative throughout the real continuation interval. -/
noncomputable section
namespace PlanarHom.BooleanEigenvalueBranches

def root (a w y : ℝ) : ℝ := Real.sqrt (a^2+w^2*y)
def plus (c a w y : ℝ) : ℝ := c+root a w y
def minus (c a w y : ℝ) : ℝ := c-root a w y
def ratio (c a w y : ℝ) : ℝ := minus c a w y/plus c a w y
def logRatio (c a w y : ℝ) : ℝ := Real.log (ratio c a w y)

theorem branches_positive (c a w y : ℝ) (hc : 0<c) (hca : c^2-a^2=1)
    (ha : 0<a^2+w^2*y) (hy : w^2*y<1) :
    0<minus c a w y ∧ 0<plus c a w y ∧ 0<ratio c a w y ∧ ratio c a w y<1 := by
  have hs : 0<root a w y := Real.sqrt_pos.mpr ha
  have hsq : (root a w y)^2=a^2+w^2*y := Real.sq_sqrt ha.le
  have hlt : root a w y<c := by nlinarith
  have hm : 0<minus c a w y := sub_pos.mpr hlt
  have hp : 0<plus c a w y := add_pos hc hs
  refine ⟨hm,hp,div_pos hm hp,?_⟩
  apply (div_lt_one hp).mpr
  change c-root a w y<c+root a w y
  linarith

theorem hasDerivAt_root (a w y : ℝ) (ha : 0<a^2+w^2*y) :
    HasDerivAt (root a w) (w^2/(2*root a w y)) y := by
  have hg : HasDerivAt (fun t : ℝ=>a^2+w^2*t) (w^2) y := by
    simpa only [zero_add,mul_one,Pi.add_apply] using (hasDerivAt_const y (a^2)).add ((hasDerivAt_id y).const_mul (w^2))
  have h := (Real.hasDerivAt_sqrt (ne_of_gt ha)).comp y hg
  convert h using 1 <;> simp only [root,Function.comp_def] <;> ring

/-- The exact derivative used after the substitution y=x². It holds wherever
both eigenvalues are positive, including negative y above the branch point. -/
theorem hasDerivAt_logRatio (c a w y : ℝ) (hc : 0<c) (hca : c^2-a^2=1)
    (ha : 0<a^2+w^2*y) (hy : w^2*y<1) :
    HasDerivAt (logRatio c a w)
      (-c*w^2/(root a w y*(1-w^2*y))) y := by
  have hb := branches_positive c a w y hc hca ha hy
  have hr := hasDerivAt_root a w y ha
  have hm : HasDerivAt (minus c a w) (-(w^2/(2*root a w y))) y := by
    simpa only [minus,zero_sub] using (hasDerivAt_const y c).sub hr
  have hp : HasDerivAt (plus c a w) (w^2/(2*root a w y)) y := by
    simpa only [plus,zero_add] using (hasDerivAt_const y c).add hr
  have hl := (hm.div hp (ne_of_gt hb.2.1)).log (ne_of_gt hb.2.2.1)
  have hs : root a w y≠0 := ne_of_gt (Real.sqrt_pos.mpr ha)
  have hsquare : (root a w y)^2=a^2+w^2*y := Real.sq_sqrt ha.le
  have hh : 1-w^2*y≠0 := ne_of_gt (sub_pos.mpr hy)
  have hn : c-root a w y≠0 := ne_of_gt hb.1
  have hd : c+root a w y≠0 := ne_of_gt hb.2.1
  have hdif : (c-root a w y)*(c+root a w y)=1-w^2*y := by nlinarith [hsquare]
  convert hl using 1
  simp only [minus,plus,Pi.div_apply]
  symm
  calc
    _ = -c*w^2/(root a w y*((c-root a w y)*(c+root a w y))) := by
      field_simp [hs,hn,hd]
      ring
    _ = _ := by rw [hdif]

theorem logRatio_eq_log_sub (c a w y : ℝ) (hc : 0<c) (hca : c^2-a^2=1)
    (ha : 0<a^2+w^2*y) (hy : w^2*y<1) :
    logRatio c a w y=Real.log (minus c a w y)-Real.log (plus c a w y) := by
  have hb := branches_positive c a w y hc hca ha hy
  exact Real.log_div (ne_of_gt hb.1) (ne_of_gt hb.2.1)

def cParameter (θ : ℝ) (t : ℕ) : ℝ := (θ^t+(θ^t)⁻¹)/2
def aParameter (θ : ℝ) (t : ℕ) : ℝ := (θ^t-(θ^t)⁻¹)/2

theorem parameter_identity (θ : ℝ) (t : ℕ) (hθ : θ≠0) :
    (cParameter θ t)^2-(aParameter θ t)^2=1 := by
  have hp : θ^t≠0 := pow_ne_zero _ hθ
  unfold cParameter aParameter
  field_simp
  ring

theorem cParameter_pos {θ : ℝ} (hθ : 0<θ) (t : ℕ) : 0<cParameter θ t :=
  div_pos (add_pos (pow_pos hθ t) (inv_pos.mpr (pow_pos hθ t))) (by norm_num)

theorem aParameter_pos {θ : ℝ} {t : ℕ} (hθ : 1<θ) (ht : 0<t) : 0<aParameter θ t := by
  have hp : 1<θ^t := one_lt_pow₀ hθ (Nat.ne_of_gt ht)
  have hi : (θ^t)⁻¹<1 := inv_lt_one_of_one_lt₀ hp
  exact div_pos (sub_pos.mpr (hi.trans hp)) (by norm_num)

@[simp] theorem aParameter_one (t : ℕ) : aParameter 1 t=0 := by simp [aParameter]
@[simp] theorem cParameter_one (t : ℕ) : cParameter 1 t=1 := by norm_num [cParameter]

theorem aParameter_ne_zero_iff {θ : ℝ} {t : ℕ} (hθ : 1≤θ) (ht : 0<t) :
    aParameter θ t≠0 ↔ 1<θ := by
  constructor
  · intro hn
    rcases lt_or_eq_of_le hθ with h|h
    · exact h
    · subst θ
      exact (hn (aParameter_one t)).elim
  · intro h
    exact ne_of_gt (aParameter_pos h ht)

theorem aParameter_nonneg {θ : ℝ} (hθ : 1≤θ) (t : ℕ) : 0≤aParameter θ t := by
  rcases Nat.eq_zero_or_pos t with rfl|ht
  · simp [aParameter]
  rcases lt_or_eq_of_le hθ with h|h
  · exact (aParameter_pos h ht).le
  · subst θ
    simp

def bParameter (θ w : ℝ) (t : ℕ) : ℝ := (aParameter θ t/w)^2

end PlanarHom.BooleanEigenvalueBranches
