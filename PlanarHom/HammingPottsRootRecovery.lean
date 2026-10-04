import PlanarHom.HammingPottsTensorPartition
import PlanarHom.PositiveFieldPowerRootMachines
import PlanarHom.FixedPowerMachines
import PlanarHom.MaterializedFieldListMachines

/-! NEW exact fixed-positive-root recovery of one Potts partition value from
the literal selected tensor, with unconditional compiled field arithmetic. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.HammingPottsRootRecovery
open HammingPottsTensorPartition HammingPottsFieldFamily HammingPottsProductIdentities
open Complexity PairProjectionMachines
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension d : ℕ}

def recover (basis : Module.Basis (Fin dimension) ℚ K) (sizes : Fin d→ℕ) (s : ℕ)
    (p : ℕ×List K) : K :=
  PositiveFieldPowerRootMachines.root basis K.val.toRingHom (selectedMultiplicity sizes s)
    (p.2.sum/(discardedColors sizes s:K)^p.1)

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K) (sizes : Fin d→ℕ) (s : ℕ) :
    FP (BitEncoding.unaryNat.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis)
      (recover basis sizes s) := by
  have hn:=fp_fst BitEncoding.unaryNat (numberFieldEncoding basis).list
  have hs:=(fp_snd BitEncoding.unaryNat (numberFieldEncoding basis).list).comp
    (MaterializedFieldListMachines.fp_sum basis)
  have hd:=hn.comp (FixedPowerMachines.fp_power basis (discardedColors sizes s:K))
  exact ((hs.pair hd).comp (FixedFieldArithmetic.fp_division basis)).comp
    (PositiveFieldPowerRootMachines.fp_root basis K.val.toRingHom (selectedMultiplicity sizes s))

theorem potts_partition_nonnegative {V E : Type*} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (s : ℕ) :
    0 ≤ K.val.toRingHom (G.partition
      (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) K) (fun _=>1)) := by
  simp only [MultiGraph.partition,MultiGraph.assignmentWeight_one]
  change 0 ≤ K.val.toRingHom (∑ σ : V→Fin s, ∏a,
    (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) K)
      (σ (G.src a)) (σ (G.dst a)))
  rw [map_sum]
  apply Finset.sum_nonneg
  intro σ _
  rw [map_prod]
  apply Finset.prod_nonneg
  intro a _
  by_cases h : σ (G.src a)=σ (G.dst a)
  · rw [FullLogarithmicProductIdentities.pottsMatrix,if_pos h,map_ofNat]
    norm_num
  · rw [FullLogarithmicProductIdentities.pottsMatrix,if_neg h,map_one]
    norm_num

theorem recover_partition {V E : Type*} [Fintype V] [Fintype E]
    (basis : Module.Basis (Fin dimension) ℚ K) (G : MultiGraph V E) {q : ℕ}
    (sizes : Fin d→ℕ) (hsizes : ∀r,0<sizes r) (s : ℕ) (hoccurs : ∃r,sizes r=s)
    (e : Fin q≃Color sizes) :
    recover basis sizes s (Fintype.card V,[G.partition (targetK sizes s e) (fun _=>1)]) =
      G.partition (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) K)
        (fun _=>1) := by
  have hℓ : (discardedColors sizes s:K) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (discardedColors_pos sizes s hsizes))
  simp only [recover,List.sum_cons,List.sum_nil,add_zero,target_partition]
  rw [mul_comm ((discardedColors sizes s:K)^Fintype.card V),
    mul_div_cancel_right₀ _ (pow_ne_zero _ hℓ)]
  exact PositiveFieldPowerRootMachines.root_pow_of_nonnegative basis K.val.toRingHom
    (selectedMultiplicity sizes s) (selectedMultiplicity_pos sizes s hoccurs) _
    (potts_partition_nonnegative G s)

end PlanarHom.HammingPottsRootRecovery
