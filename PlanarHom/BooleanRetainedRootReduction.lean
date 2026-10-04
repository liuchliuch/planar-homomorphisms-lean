import PlanarHom.BooleanTensorSpectral
import PlanarHom.BooleanRetainedTensor
import PlanarHom.HammingPottsTensorPartition
import PlanarHom.PositiveFieldPowerRootMachines
import PlanarHom.FixedPowerMachines
import PlanarHom.MaterializedFieldListMachines
import PlanarHom.PottsComponentCode
import PlanarHom.GraphComponentMachines
import PlanarHom.HeterogeneousGraphReduction
import PlanarHom.RootedHomogeneousSemantics

/-! NEW actual positive-root reduction from one Boolean factor to its retained
identity tensor. The component factor is computed from the literal graph, so
isolates, loops, duplicate edges and the empty graph are covered. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanRetainedRootReduction
open Complexity Complexity.MixedCode PairProjectionMachines
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension d q : ℕ}

def matrix (e : Fin q≃(Fin d→Bool)) (S : Finset (Fin d)) (B : Matrix Bool Bool K) :
    Matrix (Fin q) (Fin q) K :=
  fun i j=>BooleanTensorSpectral.tensor (fun r=>if r∈S then B else 1) (e i) (e j)

theorem partition_matrix {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E)
    (e : Fin q≃(Fin d→Bool)) (S : Finset (Fin d)) (B : Matrix Bool Bool K) :
    G.partition (matrix e S B) (fun _=>1)=
      ((2:K)^(d-S.card))^(G.componentCount Finset.univ) * (G.partition B (fun _=>1))^S.card := by
  change G.partition (fun i j=>BooleanTensorSpectral.tensor (fun r=>if r∈S then B else 1) (e i) (e j)) (fun _=>1)=_
  rw [G.partition_reindexColors _ (fun _ : (Fin d→Bool)=>1) e]
  change G.partition (HammingKernelTensor.tensor (fun r=>if r∈S then B else 1)) (fun _=>1)=_
  rw [HammingPottsTensorPartition.partition_tensor]
  have hf:(fun r:Fin d=>G.partition (if r∈S then B else 1) (fun _=>1))=
      fun r=>if r∈S then G.partition B (fun _=>1) else G.partition (1:Matrix Bool Bool K) (fun _=>1):=by
    funext r
    split <;> rfl
  rw [hf,Finset.prod_ite]
  simp only [Finset.filter_univ_mem,Finset.prod_const]
  have hi:G.partition (1:Matrix Bool Bool K) (fun _=>1)=(2:K)^(G.componentCount Finset.univ):=by
    simpa only [Fintype.card_bool,Nat.cast_ofNat] using
      BooleanRetainedTensor.unweighted_identity (C:=Bool) (R:=K) G
  rw [hi]
  have hc:(Finset.univ.filter (fun r:Fin d=>r∉S))=Sᶜ:=by ext r;simp
  rw [hc,Finset.card_compl,Fintype.card_fin,←pow_mul,←pow_mul]
  ring

def prepare (g : MixedCode) : ℕ×List MixedCode := ((GraphComponentCode.parts g).length,[g])

theorem fp_prepare : FP encoding (BitEncoding.unaryNat.prod encoding.list) prepare := by
  have hc:=GraphComponentMachines.fp_parts.comp
    (ListUnaryLengthMachine.fp_length BitEncoding.nat.list)
  have hq:=((fp_id encoding).pair (fp_const encoding encoding.list [])).comp
    (ListMutationMachines.fp_cons encoding)
  exact hc.pair hq

def recover (basis : Module.Basis (Fin dimension) ℚ K) (S : Finset (Fin d))
    (p : ℕ×List K) : K :=
  PositiveFieldPowerRootMachines.root basis K.val.toRingHom S.card
    (p.2.sum/((2:K)^(d-S.card))^p.1)

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K) (S : Finset (Fin d)) :
    FP (BitEncoding.unaryNat.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis)
      (recover basis S) := by
  have hn:=fp_fst BitEncoding.unaryNat (numberFieldEncoding basis).list
  have hs:=(fp_snd BitEncoding.unaryNat (numberFieldEncoding basis).list).comp
    (MaterializedFieldListMachines.fp_sum basis)
  have hd:=hn.comp (FixedPowerMachines.fp_power basis ((2:K)^(d-S.card)))
  exact ((hs.pair hd).comp (FixedFieldArithmetic.fp_division basis)).comp
    (PositiveFieldPowerRootMachines.fp_root basis K.val.toRingHom S.card)

theorem partition_nonnegative {V E : Type} [Fintype V] [Fintype E] (G : MultiGraph V E)
    (B : Matrix Bool Bool K) (hB:∀i j,0≤(B i j : ℝ)) :
    0≤K.val.toRingHom (G.partition B (fun _=>1)) := by
  simp only [MultiGraph.partition,MultiGraph.assignmentWeight_one,map_sum,map_prod]
  exact Finset.sum_nonneg (fun σ _=>Finset.prod_nonneg (fun a _=>hB _ _))

theorem recover_partition {V E : Type} [Fintype V] [Fintype E]
    (basis : Module.Basis (Fin dimension) ℚ K) (G : MultiGraph V E)
    (e : Fin q≃(Fin d→Bool)) (S : Finset (Fin d)) (hS:S.Nonempty)
    (B : Matrix Bool Bool K) (hB:∀i j,0≤(B i j : ℝ)) :
    recover basis S (G.componentCount Finset.univ,[G.partition (matrix e S B) (fun _=>1)])=
      G.partition B (fun _=>1) := by
  simp only [recover,List.sum_cons,List.sum_nil,add_zero,partition_matrix]
  rw [mul_div_cancel_left₀ _ (pow_ne_zero _ (pow_ne_zero _ (by norm_num : (2:K)≠0)))]
  exact PositiveFieldPowerRootMachines.root_pow_of_nonnegative basis K.val.toRingHom S.card
    hS.card_pos _ (partition_nonnegative G B hB)

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (e : Fin q≃(Fin d→Bool)) (S : Finset (Fin d)) (hS:S.Nonempty)
    (B : Matrix Bool Bool K) (hB:∀i j,0≤(B i j : ℝ)) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1=>B) (fun u:Fin 0=>u.elim0) (fun _=>1))
      (evaluationProblem basis (fun _ : Fin 1=>matrix e S B) (fun u:Fin 0=>u.elim0) (fun _=>1)) := by
  apply planarReductionOfHeterogeneousPipeline basis BitEncoding.unaryNat
    (fun _:Fin 1=>B) (fun u:Fin 0=>u.elim0) (fun _=>1)
    (fun _:Fin 1=>matrix e S B) (fun u:Fin 0=>u.elim0) (fun _=>1)
    prepare (recover basis S) fp_prepare (fp_recover basis S) ?_ ?_
  · intro g hg z hz
    obtain rfl:=List.mem_singleton.mp hz
    exact hg
  · intro g hg
    simp only [prepare,List.map_cons,List.map_nil,totalEvaluation_valid _ _ _ _ hg.1]
    rw [evaluate_homogeneous,evaluate_homogeneous,←GraphComponentCode.componentCount_eq_parts_length g hg.1]
    exact recover_partition basis (g.toMultiGraph hg.1) e S hS B hB

end PlanarHom.BooleanRetainedRootReduction
