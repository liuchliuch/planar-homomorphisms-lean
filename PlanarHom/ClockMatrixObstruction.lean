import PlanarHom.CenteredLogStructural
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! Pure real clock obstruction. The two-outer-product upper bound suffices
for the complete state-count exclusion, without an additional Fourier rank
calculation. It covers both signs of the nonzero coupling. -/
noncomputable section
open Classical
namespace PlanarHom.ClockModel
open Structures CenteredLogTensorExpansion

def angle (q:ℕ) (i:Fin q) : ℝ := 2*Real.pi*(i.val:ℝ)/(q:ℝ)
def interaction (q:ℕ) (K:ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  fun i j=>Real.exp (K*Real.cos (angle q i-angle q j))

theorem angle_nonnegative {q:ℕ} (i:Fin q) : 0≤angle q i := by unfold angle; positivity

theorem angle_lt_two_pi {q:ℕ} (i:Fin q) : angle q i < 2*Real.pi := by
  have hq:0 < (q:ℝ):=by exact_mod_cast lt_of_le_of_lt (Nat.zero_le _) i.isLt
  have hi:(i.val:ℝ)<q:=by exact_mod_cast i.isLt
  apply (div_lt_iff₀ hq).mpr
  nlinarith [Real.pi_pos]

theorem angle_injective (q:ℕ) : Function.Injective (angle q) := by
  intro i j he
  have hq:(q:ℝ)≠0:=by exact_mod_cast (Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) i.isLt))
  have hp:2*Real.pi≠0:=ne_of_gt (by positivity)
  have hval : (i.val:ℝ)=(j.val:ℝ) := mul_left_cancel₀ hp ((div_left_inj' hq).mp he)
  exact Fin.ext (by exact_mod_cast hval)

theorem cos_difference_eq_one_iff {q:ℕ} (i j:Fin q) :
    Real.cos (angle q i-angle q j)=1 ↔ i=j := by
  have hlo : -(2*Real.pi)<angle q i-angle q j := by
    linarith [angle_nonnegative i,angle_lt_two_pi j]
  have hhi : angle q i-angle q j<2*Real.pi := by
    linarith [angle_lt_two_pi i,angle_nonnegative j]
  rw [Real.cos_eq_one_iff_of_lt_of_lt hlo hhi,sub_eq_zero]
  exact (angle_injective q).eq_iff

theorem symmetric (q:ℕ) (K:ℝ) (i j:Fin q) : interaction q K i j=interaction q K j i := by
  unfold interaction
  rw [show angle q j-angle q i= -(angle q i-angle q j) by ring,Real.cos_neg]

theorem positive (q:ℕ) (K:ℝ) (i j:Fin q) : 0 < interaction q K i j := Real.exp_pos _

theorem diagonal (q:ℕ) (K:ℝ) (i:Fin q) : interaction q K i i=Real.exp K := by
  simp [interaction]

theorem rows_injective {q:ℕ} {K:ℝ} (hK:K≠0) : Function.Injective (interaction q K) := by
  intro i j h
  have hh:=congrFun h i
  rw [diagonal] at hh
  change Real.exp K=Real.exp (K*Real.cos (angle q j-angle q i)) at hh
  have he:Real.cos (angle q j-angle q i)=1 := by
    have he:=Real.exp_injective hh
    exact (mul_left_cancel₀ hK (by simpa only [mul_one] using he.symm))
  exact ((cos_difference_eq_one_iff j i).mp he).symm

theorem log_outer_decomposition (q:ℕ) (K:ℝ) :
    entrywiseLog (interaction q K)=
      Matrix.vecMulVec (fun i=>K*Real.cos (angle q i)) (fun i=>Real.cos (angle q i))+
      Matrix.vecMulVec (fun i=>K*Real.sin (angle q i)) (fun i=>Real.sin (angle q i)) := by
  ext i j
  simp only [entrywiseLog,interaction,Real.log_exp,Real.cos_sub,Matrix.add_apply,Matrix.vecMulVec_apply]
  ring

theorem centered_log_rank_le_two (q:ℕ) (K:ℝ) :
    (sourceCentering q*entrywiseLog (interaction q K)*sourceCentering q).rank≤2 := by
  have hlog : (entrywiseLog (interaction q K)).rank≤2 := by
    let X:Matrix (Fin q) (Fin 2) ℝ:=fun i=>![K*Real.cos (angle q i),K*Real.sin (angle q i)]
    let Y:Matrix (Fin 2) (Fin q) ℝ:=![fun j=>Real.cos (angle q j),fun j=>Real.sin (angle q j)]
    have he:entrywiseLog (interaction q K)=X*Y := by
      ext i j
      simp only [entrywiseLog,interaction,Real.log_exp,Real.cos_sub,Matrix.mul_apply,Fin.sum_univ_two]
      simp [X,Y]
      ring
    rw [he]
    exact (Matrix.rank_mul_le_left X Y).trans (by simpa using Matrix.rank_le_card_width X)
  exact (Matrix.rank_mul_le_left _ _).trans ((Matrix.rank_mul_le_right _ _).trans hlog)

theorem weighted_class_necessary {q:ℕ} (hq:2≤q) {K:ℝ} (hK:K≠0)
    (w:Fin q→ℝ) (hw:∀i,0 < w i)
    (h:PositiveVertexWeightClass (interaction q K) w (symmetric q K)) :
    (q=2 ∨ q=4) ∧ ∃μ:ℝ,0 < μ ∧ ∀i,w i=μ := by
  letI : Nonempty (Fin q):=⟨⟨0,by omega⟩⟩
  obtain ⟨d,e,γ,μ,ρ,hqd,hγ,hμ,hρ,hm,hw',hr⟩:=
    CenteredLogStructural.lemma124_structure_and_rank (interaction q K) w (symmetric q K)
      (positive q K) (fun i j=>(diagonal q K i).trans (diagonal q K j).symm)
      (rows_injective hK) hw h
  have hd:d≤2:=by rw [←hr]; exact centered_log_rank_le_two q K
  refine ⟨?_,μ,hμ,hw'⟩
  interval_cases d <;> norm_num at hqd <;> omega

theorem zero_interaction (q:ℕ) : interaction q 0=fun _ _=>1 := by
  ext i j; simp [interaction]

end PlanarHom.ClockModel
