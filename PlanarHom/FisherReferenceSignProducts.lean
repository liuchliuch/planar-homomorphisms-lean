import PlanarHom.FisherCubicWeightSemantics
import PlanarHom.FisherMatchingBoundary
import PlanarHom.OccurrencePfaffianPairings

/-! NEW explicit product form of the original crossing-number matching sign.
Only proved occurrence injectivity of the actual reference matching is used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
variable {V E R : Type*} [LinearOrder V] [CommRing R]
local instance (priority := high) referencePairDecEq : DecidableEq (V×V) := Classical.decEq (V×V)

 theorem pairingSign_eq_product (P : Finset (V×V)) :
    (pairingSign P : R)=∏p∈P,∏q∈P,if p.1<q.1 ∧ q.1<p.2 ∧ p.2<q.2 then (-1:R) else 1 := by
  simp only [pairingSign,pairingCrossings,Int.cast_pow,Int.cast_neg,Int.cast_one]
  rw [←Finset.prod_const,Finset.prod_filter,Finset.prod_product]

 theorem matchingPfaffianSign_eq_products (G : MultiGraph V E) (orientation : E→Bool)
    (M : Finset E) (hM : G.PerfectMatching M) :
    G.matchingPfaffianSign (R:=R) orientation M=
      (∏e∈M,∏f∈M,if (G.canonicalPair e).1<(G.canonicalPair f).1 ∧
        (G.canonicalPair f).1<(G.canonicalPair e).2 ∧ (G.canonicalPair e).2<(G.canonicalPair f).2 then (-1:R) else 1)*
      ∏e∈M,G.canonicalSign orientation e := by
  have hinj:=hM.injOn_edgeMap G (pairGraph V) G.canonicalPair G.canonicalPair_endpointCount
  rw [matchingPfaffianSign,pairingSign_eq_product,Finset.prod_image hinj]
  apply congrArg₂ (·*·) _ rfl
  apply Finset.prod_congr rfl
  intro e he
  exact Finset.prod_image hinj

end PlanarHom.MultiGraph
