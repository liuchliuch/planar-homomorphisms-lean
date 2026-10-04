import PlanarHom.PottsRandomClusterParallel

/-! Exact normalization of the diagonal Tutte value supplied by the intended
radial coefficient theorem. The value is defined from the independent literal
rank-subset Tutte polynomial, never from the desired recovery answer. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsTwoStageInterpolation
open MultiGraph
variable {V E : Type} [Fintype V] [Fintype E]

def radialValue (G : MultiGraph V E) (δ : ℚ) (k : ℕ) : ℚ :=
  δ^(k*G.componentCount Finset.univ)*G.rankSubsetTutte (1+δ^k) (1+δ^k)

/-- Every exponent is justified by the actual component-rank bounds, including
isolates, loops and parallel occurrences. No division or nonzero premise occurs. -/
theorem normalize_radialValue (G : MultiGraph V E) (δ : ℚ) (k : ℕ) :
    (δ^k)^Fintype.card V*radialValue G δ k=
      G.randomCluster ((δ^k)^2) (δ^k) := by
  let d := δ^k
  rw [radialValue,pow_mul,rankSubsetTutte_eq_component_sum,randomCluster]
  simp only [add_sub_cancel_left]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have hc := G.component_exponents_nonnegative A
  change d^Fintype.card V*(d^G.componentCount Finset.univ*
    (d^(G.componentCount A-G.componentCount Finset.univ)*
      d^(A.card+G.componentCount A-Fintype.card V)))=(d^2)^G.componentCount A*d^A.card
  calc
    _ = d^(Fintype.card V+G.componentCount Finset.univ+
        (G.componentCount A-G.componentCount Finset.univ)+
        (A.card+G.componentCount A-Fintype.card V)) := by simp only [pow_add]; ring
    _ = d^(2*G.componentCount A+A.card) := by congr 1; omega
    _ = _ := by rw [pow_add,pow_mul]
end PlanarHom.PottsTwoStageInterpolation

namespace PlanarHom.Complexity.MixedCode
open MultiGraph PottsTwoStageInterpolation

/-- Literal parallel source graphs give precisely the edge nodes used by the
row-major recovery machine. This closes the arithmetic two-stage source law. -/
theorem normalize_radialValue_parallel (g : MixedCode) (hg : g.Valid 1 0)
    (δ : ℚ) (k l : ℕ) :
    (δ^k)^g.vertices*
      radialValue ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)) δ k=
      (g.toMultiGraph hg).randomCluster ((δ^k)^2) ((1+δ^k)^l-1) := by
  have h := normalize_radialValue
    ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)) δ k
  rw [randomCluster_parallelCode] at h
  simpa only [Fintype.card_fin,parallelLabel] using h
end PlanarHom.Complexity.MixedCode
