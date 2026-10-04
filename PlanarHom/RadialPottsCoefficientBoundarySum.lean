import PlanarHom.RadialPottsBoundaryPermutation
import PlanarHom.RadialPottsCoefficientStateSum
import PlanarHom.PottsCenteredDegreeTwo

/-! Actual all-k radial coefficient evaluation as a boundary-permutation state
sum. All normalization, cancellation, multiplicity and degree-two evaluations
are proved for the literal occurrence assembly. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile PottsCentered
variable {E : Type} [Fintype E] {k : ℕ}

theorem selectedValue_boundaryPermutation (rotation : Equiv.Perm (Medial.Dart E))
    (choice : E → Bool) (q : ℕ) (hq : 0<q) :
    selectedValue (graph rotation k) q (stateEdges choice)=
      ((q:ℚ)-1)^((permutationGraph (boundaryPermutation rotation choice)).componentCount Finset.univ*k) := by
  rw [selectedValue_stateGraph,normalized_degree_two _ q hq (stateGraph_degree_two rotation choice),
    state_componentCount_boundaryPermutation]

def boundaryStateSum (rotation : Equiv.Perm (Medial.Dart E)) (δ : ℚ) (k : ℕ) : ℚ :=
  ∑ choice : E → Bool,δ^((permutationGraph (boundaryPermutation rotation choice)).componentCount Finset.univ*k)

theorem filteredStateSum_eq_boundaryStateSum (rotation : Equiv.Perm (Medial.Dart E))
    (q : ℕ) (hq : 0<q) (hk : 0<k) :
    filteredStateSum rotation q k=boundaryStateSum rotation ((q:ℚ)-1) k := by
  rw [filteredStateSum_eq rotation q hq hk]
  exact Finset.sum_congr rfl (fun choice _ => selectedValue_boundaryPermutation rotation choice q hq)

theorem marked_coefficient_eq_boundaryStateSum (rotation : Equiv.Perm (Medial.Dart E))
    (q N : ℕ) (hq : 0<q) (hk : 0<k) (hN : (Finset.univ\longEdges E k).card<N) :
    (markedPolynomial (graph rotation k) q (longEdges E k) N).coeff
      (N*(longEdges E k).card+2*k^2*Fintype.card E)=boundaryStateSum rotation ((q:ℚ)-1) k := by
  rw [marked_coefficient_eq_filtered rotation q N hN,filteredStateSum_eq_boundaryStateSum rotation q hq hk]
end PlanarHom.RadialPotts.Assembly
