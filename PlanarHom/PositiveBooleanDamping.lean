import PlanarHom.WheatstoneSupport
import PlanarHom.CubeGraphMetric

/-! NEW rational Schur damping of an arbitrary positive symmetric matrix.
A sufficiently small rational parameter gives a positive-definite member, and
one positive sample suffices to undo a Boolean tensor damping exactly. -/
noncomputable section
open Classical
open scoped BigOperators Topology
namespace PlanarHom.PositiveBooleanDamping
open Filter
variable {V:Type} [Fintype V] [DecidableEq V]

def damped (G:SimpleGraph V) (N:Matrix V V ℝ) (t:ℝ) : Matrix V V ℝ :=
  fun i j=>N i j*t^(G.dist i j)

theorem damped_symmetric (G:SimpleGraph V) (N:Matrix V V ℝ) (hN:N.IsHermitian) (t:ℝ) :
    (damped G N t).IsHermitian := by
  ext i j
  have hs:N j i=N i j:=by simpa only [star_trivial] using hN.apply i j
  simp [damped,Matrix.conjTranspose_apply,star_trivial,SimpleGraph.dist_comm,hs]

theorem continuous_damped (G:SimpleGraph V) (N:Matrix V V ℝ) : Continuous (damped G N) := by
  apply continuous_matrix
  intro i j
  exact continuous_const.mul (continuous_id.pow _)

theorem eventually_posDef (G:SimpleGraph V) (hG:G.Connected) (N:Matrix V V ℝ)
    (hN:N.IsHermitian) (hdiag:∀i,0<N i i) :
    ∀ᶠt:ℝ in 𝓝 0,(damped G N t).PosDef := by
  have he (i:V):∀ᶠt:ℝ in 𝓝 0,
      (∑j∈Finset.univ.erase i,‖damped G N t i j‖)<damped G N t i i := by
    have hsum:Continuous (fun t:ℝ=>∑j∈Finset.univ.erase i,‖damped G N t i j‖):=
      continuous_finset_sum _ (fun j _=>((continuous_damped G N).matrix_elem i j).norm)
    apply Filter.Tendsto.eventually_lt hsum.continuousAt ((continuous_damped G N).matrix_elem i i).continuousAt
    have hz:(∑j∈Finset.univ.erase i,‖damped G N 0 i j‖)=0:=by
      apply Finset.sum_eq_zero
      intro j hj
      have hij:i≠j:=Ne.symm (Finset.mem_erase.mp hj).1
      have hdist:G.dist i j≠0:=fun h=>hij ((hG.dist_eq_zero_iff).mp h)
      simp [damped,zero_pow hdist]
    dsimp only
    rw [hz]
    simpa [damped,SimpleGraph.dist_self] using hdiag i
  filter_upwards [Filter.eventually_all.mpr he] with t ht
  exact WheatstoneCoefficients.posDef_of_rowSum_lt_diagonal (damped_symmetric G N hN t) ht

theorem exists_rational_posDef (G:SimpleGraph V) (hG:G.Connected) (N:Matrix V V ℝ)
    (hN:N.IsHermitian) (hpos:∀i j,0<N i j) :
    ∃t:ℚ,0<t ∧ (t:ℝ)<1 ∧ (damped G N (t:ℝ)).PosDef ∧
      (∀i j,0<damped G N (t:ℝ) i j) := by
  obtain ⟨t,ht,ht1,hpd⟩:=WheatstoneCoefficients.exists_positive_rat_of_eventually
    (Filter.Eventually.filter_mono nhdsWithin_le_nhds (eventually_posDef G hG N hN (fun i=>hpos i i)))
    (by norm_num : (0:ℝ)<1)
  exact ⟨t,ht,ht1,hpd,fun i j=>mul_pos (hpos i j) (pow_pos (by exact_mod_cast ht) _)⟩

theorem undo_tensor {d:ℕ} (B:Matrix (Boolean.Cube d) (Boolean.Cube d) ℝ)
    (t:ℝ) (ht:0<t) (γ:ℝ) (ρ:Fin d→ℝ)
    (h: (fun i j=>B i j*Boolean.tensor (fun _=>t) i j)=γ • Boolean.tensor ρ) :
    B=γ • Boolean.tensor (fun r=>ρ r/t) := by
  funext i j
  apply (mul_right_cancel₀ (ne_of_gt (Boolean.tensor_pos (fun _=>ht) i j)))
  have hp:=congrFun (congrFun h i) j
  change B i j*Boolean.tensor (fun _=>t) i j=
    (γ*Boolean.tensor (fun r=>ρ r/t) i j)*Boolean.tensor (fun _=>t) i j
  rw [mul_assoc,←Boolean.tensor_mul]
  simp only [div_mul_cancel₀ _ ht.ne']
  exact hp

end PlanarHom.PositiveBooleanDamping
