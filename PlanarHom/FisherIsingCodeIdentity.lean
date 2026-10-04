import PlanarHom.FisherCodePipeline
import PlanarHom.FixedPowerMachines

/-! Literal Ising normalization for the compiled two-stage Fisher graph. The
high-temperature edge parameter may be negative or zero. -/
namespace PlanarHom.FisherCodePipeline
open Complexity PairProjectionMachines MultiGraph
variable {K:Type} [Field K] [Algebra ℚ K] {dimension:ℕ}
variable (basis:Module.Basis (Fin dimension) ℚ K)

def normalization (ρ:K) (g:MixedCode):K:=((1+ρ)/2)^g.edges.length/(2^g.vertices)

theorem fp_normalization (ρ:K):FP MixedCode.encoding (numberFieldEncoding basis) (normalization ρ):=by
  have hm:=MixedCode.fp_edges.comp (ListUnaryLengthMachine.fp_length PlanarityOrientedForest.edgeCode)
  have hn:=MixedCode.fp_vertices
  exact ((hm.comp (FixedPowerMachines.fp_power basis ((1+ρ)/2))).pair
    (hn.comp (FixedPowerMachines.fp_power basis 2))).comp (FixedFieldArithmetic.fp_division basis)

theorem ising_matching_identity (φ:K→+*ℝ) {g:MixedCode} {bt ut:ℕ}
    (hg:g.Valid bt ut) (ρ:K) (hρ:1+φ ρ≠0):
    (g.toMultiGraph hg).partition (Boolean.W (φ ρ)) (fun _=>1)=
      φ (normalization ρ g) *
        ((code g).toMultiGraph (valid hg)).perfectMatchingSum
          (fun e=>φ ((isingData ρ g).2.getD e.val 0)):=by
  have hm:=matching_identity φ hg (isingWeights ρ g)
  simp only [isingWeights_get,map_div₀,map_sub,map_one] at hm
  change ((code g).toMultiGraph _).perfectMatchingSum (fun e=>φ ((isingData ρ g).2.getD e.val 0))=_ at hm
  rw [hm,(g.toMultiGraph hg).ising_evenSubgraph_expansion (φ ρ) hρ]
  simp only [Fintype.card_fin,normalization,map_div₀,map_pow,map_add,map_one,map_ofNat]
  have hp:(4:ℝ)^g.vertices=2^g.vertices*2^g.vertices:=by rw [←mul_pow]; norm_num
  rw [hp]
  have hn:(2:ℝ)^g.vertices≠0:=pow_ne_zero _ (by norm_num)
  field_simp

end PlanarHom.FisherCodePipeline
