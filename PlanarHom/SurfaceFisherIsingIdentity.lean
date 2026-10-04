import PlanarHom.SurfaceFisherCodeSemantics
import PlanarHom.SurfaceFisherCodeMachines
import PlanarHom.FisherIsingCodeIdentity

/-! NEW exact supplied-row Fisher/Ising weight identity and normalization.
This is independent of any genus, orientation or computational assumption. -/
noncomputable section
namespace PlanarHom.SurfaceFisherCode
open Complexity MultiGraph Fisher PlanarityLRRealization
variable {K : Type} [Field K] [Algebra ℚ K]
variable (φ : K→+*ℝ) (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hr : PlanarityRowFaceCode.Realizes g hg rows R)

theorem matching_identity (ρ : K) :
    ((code g rows).toMultiGraph (valid g hg rows R hr)).perfectMatchingSum
      (fun e => φ ((weights ρ g rows).getD e.val 0))=
      (4:ℝ)^g.vertices*(g.toMultiGraph hg).evenSubgraphSum
        (fun _ => (1-φ ρ)/(1+φ ρ)) := by
  have hm := (FisherCubicCode.matchingSum_weights (intermediate g rows) (intermediate_valid g hg rows R hr)
    (intermediate_cubic g hg rows R hr) φ
    (FisherExpansionCode.weights g (orderRows rows) (FisherCodePipeline.isingWeights ρ g))).trans
    (FisherExpansionCode.evenSubgraphSum_weights g hg R.incidenceOrdering (orderRows_realizes g hg rows R hr) φ
      (FisherCodePipeline.isingWeights ρ g))
  simpa only [weights,code,FisherCodePipeline.isingWeights_get,map_div₀,map_sub,map_add,map_one] using hm

theorem ising_matching_identity (ρ : K) (hρ : 1+φ ρ≠0) :
    (g.toMultiGraph hg).partition (Boolean.W (φ ρ)) (fun _ => 1)=
      φ (FisherCodePipeline.normalization ρ g)*
        ((code g rows).toMultiGraph (valid g hg rows R hr)).perfectMatchingSum
          (fun e => φ ((weights ρ g rows).getD e.val 0)) := by
  rw [matching_identity φ g hg rows R hr ρ,(g.toMultiGraph hg).ising_evenSubgraph_expansion (φ ρ) hρ]
  simp only [Fintype.card_fin,FisherCodePipeline.normalization,map_div₀,map_pow,map_add,map_one,map_ofNat]
  have hp : (4:ℝ)^g.vertices=2^g.vertices*2^g.vertices := by rw [←mul_pow];norm_num
  rw [hp]
  have hn : (2:ℝ)^g.vertices≠0 := pow_ne_zero _ (by norm_num)
  field_simp

end PlanarHom.SurfaceFisherCode
