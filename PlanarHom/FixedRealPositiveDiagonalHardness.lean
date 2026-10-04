import PlanarHom.RealNonnegativeHardness
import PlanarHom.ThreeStatePositiveRank

/-! NEW A.6 consequence used by the real weighted Ising-core arguments.
The obstruction is numerical and field-independent: a positive full-rank
tractable block has just one amplitude coordinate and a constant diagonal. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealApproximation
open Structures Boolean DensePolynomial FixedRealExtension RepresentedBit

 theorem positive_fullRank_class_diagonal {C : Type} [Fintype C] [Nonempty C]
    (M : Matrix C C ℝ) (hi : LinearIndependent ℝ M) (hp : ∀i j, 0 < M i j)
    (hc : NonnegativeClass M) : ∀i j, M i i = M j j := by
  have hb := ThreeStateDimension.positive_class_allowed hp hc
  cases hb with
  | zero e hz =>
    intro i j
    exact ((hp i i).ne' (hz i i)).elim
  | positive k d hk a ρ ha hρ e hm =>
    have hk1 := RankFour.positive_amplitude_size hi hk a ρ ha e hm
    subst k
    intro i j
    have he : (e i).1 = (e j).1 := Subsingleton.elim _ _
    simp only [hm,tensor_diag,mul_one,he]
  | bipartite k l d hk hl a b ρ ha hb hρ e hm =>
    let i := e.symm (Sum.inl ⟨0,hk⟩,fun _ => false)
    have hz : M i i = 0 := by simp [hm,i,bipartiteAmplitude]
    exact ((hp i i).ne' hz).elim

 theorem positive_posDef_class_diagonal {C : Type} [Fintype C] [Nonempty C]
    (M : Matrix C C ℝ) (hpd : M.PosDef) (hp : ∀i j, 0 < M i j)
    (hc : NonnegativeClass M) : ∀i j, M i i = M j j :=
  positive_fullRank_class_diagonal M (Matrix.linearIndependent_rows_iff_isUnit.mpr hpd.isUnit) hp hc

 variable {n e q : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
 theorem positive_nonconstant_diagonal_hard
    (basis : Module.Basis (Fin e) (RationalFunction n) K) (φ : K →+* ℝ)
    (M : Matrix (Fin q) (Fin q) K)
    (hpd : (show Matrix (Fin q) (Fin q) ℝ from fun i j => φ (M i j)).PosDef)
    (hp : ∀i j, 0 < φ (M i j)) (hnon : ∃i j, M i i ≠ M j j) :
    RepresentedBit.SharpPHard (FixedRealMixedInterpolation.problem basis
      (fun _ : Fin 1 => M) (fun l : Fin 0 => l.elim0) (fun _ => 1)) := by
  obtain ⟨i,j,hij⟩ := hnon
  letI : Nonempty (Fin q) := ⟨i⟩
  apply theoremA6_hard basis φ M
  · intro a b
    apply φ.injective
    simpa using congrFun (congrFun hpd.1.eq b) a
  · exact fun a b => (hp a b).le
  · intro hc
    exact hij (φ.injective (positive_posDef_class_diagonal _ hpd hp hc i j))

end PlanarHom.FixedRealApproximation
