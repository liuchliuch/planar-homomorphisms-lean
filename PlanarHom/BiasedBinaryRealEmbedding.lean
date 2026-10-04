import PlanarHom.BiasedBinaryListCompatibility
import Mathlib.RingTheory.SimpleRing.Basic

namespace PlanarHom.BiasedBinaryProductSeparation

variable {K : Type*} [Field K] (ι : K →+* ℝ)

/-- The compatibility gate works in the actual coefficient field whenever its
chosen real embedding has positive interaction entries. This covers rational
and real-algebraic inputs without putting an order on the abstract field. -/
theorem embedded_list_counts
    (xs ys : List (Bool × Bool)) (us vs : List Bool) (a b c : K)
    (ha : 0<ι a) (hb : 0<ι b) (hc : 0<ι c) (hbias : a≠c) (hdet : a*c≠b^2)
    (helen : xs.length=ys.length) (hmlen : us.length=vs.length)
    (he : edgeProduct xs a b c=edgeProduct ys a b c)
    (hi : incidenceProduct xs (a+b) (b+c)=incidenceProduct ys (a+b) (b+c))
    (hm : bitProduct us (a+b) (b+c)=bitProduct vs (a+b) (b+c)) :
    EdgeCounts.ofPairs xs=EdgeCounts.ofPairs ys ∧
      us.count false=vs.count false ∧ us.count true=vs.count true := by
  have hbe : ι a≠ι c := fun h => hbias (ι.injective h)
  have hde : ι a*ι c≠(ι b)^2 := by
    intro h
    apply hdet
    apply ι.injective
    simpa using h
  apply list_counts_of_joint_products xs ys us vs (ι a) (ι b) (ι c)
    ha hb hc hbe hde helen hmlen
  · simpa only [edgeProduct_eq,EdgeCounts.product,map_mul,map_pow] using congrArg ι he
  · simpa only [incidenceProduct_eq,EdgeCounts.endpointProduct,EdgeCounts.product,
      map_mul,map_pow,map_add] using congrArg ι hi
  · simpa only [bitProduct_eq,map_mul,map_pow,map_add] using congrArg ι hm

/-- Literal source products in a real-embedded number field determine arbitrary
rational (or other field-valued) target edge and marked-vertex weights. -/
theorem embedded_target_compatible {T : Type*} [Field T]
    (xs ys : List (Bool × Bool)) (us vs : List Bool) (a b c : K)
    (ha : 0<ι a) (hb : 0<ι b) (hc : 0<ι c) (hbias : a≠c) (hdet : a*c≠b^2)
    (helen : xs.length=ys.length) (hmlen : us.length=vs.length)
    (he : edgeProduct xs a b c=edgeProduct ys a b c)
    (hi : incidenceProduct xs (a+b) (b+c)=incidenceProduct ys (a+b) (b+c))
    (hm : bitProduct us (a+b) (b+c)=bitProduct vs (a+b) (b+c))
    (x y z h₀ h₁ : T) :
    edgeProduct xs x y z*bitProduct us h₀ h₁=
      edgeProduct ys x y z*bitProduct vs h₀ h₁ := by
  obtain ⟨heq,h₀eq,h₁eq⟩ := embedded_list_counts ι xs ys us vs a b c ha hb hc
    hbias hdet helen hmlen he hi hm
  simp only [edgeProduct_eq,bitProduct_eq,heq,h₀eq,h₁eq]

/-- The exact signed independent-set specialization needed by a clause center
with activity -1. No interpolation machine or hardness claim is hidden here. -/
theorem embedded_signedNand_compatible
    (xs ys : List (Bool × Bool)) (us vs : List Bool) (a b c : K)
    (ha : 0<ι a) (hb : 0<ι b) (hc : 0<ι c) (hbias : a≠c) (hdet : a*c≠b^2)
    (helen : xs.length=ys.length) (hmlen : us.length=vs.length)
    (he : edgeProduct xs a b c=edgeProduct ys a b c)
    (hi : incidenceProduct xs (a+b) (b+c)=incidenceProduct ys (a+b) (b+c))
    (hm : bitProduct us (a+b) (b+c)=bitProduct vs (a+b) (b+c)) :
    edgeProduct xs (1:ℚ) 1 0*bitProduct us 1 (-1)=
      edgeProduct ys (1:ℚ) 1 0*bitProduct vs 1 (-1) :=
  embedded_target_compatible ι xs ys us vs a b c ha hb hc hbias hdet
    helen hmlen he hi hm 1 1 0 1 (-1)
end PlanarHom.BiasedBinaryProductSeparation
