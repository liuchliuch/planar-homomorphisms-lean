import PlanarHom.BiasedBinaryPrimeNormalization
import PlanarHom.ProductCompatibility

namespace PlanarHom.BiasedBinaryProductSeparation
variable {K : Type} [Field K] [Algebra ℚ K] [Module.Finite ℚ K]

/-- A single fixed endpoint activity produces a matrix whose equal-length
products determine the entire edge histogram. The prime is genuinely chosen. -/
theorem exists_prime_product_maps (ι : K →+* ℝ) (a b c : K)
    (ha : 0<ι a) (hb : 0<ι b) (hc : 0<ι c) (hdet : a*c≠b^2) :
    ∃ p : ℕ,p.Prime ∧ ∀ x y z : K,
      ProductCompatibility.HasProductMaps (K:=K) (pairWeight (F:=K) a (b*(p:K)) (c*(p:K)^2))
        (pairWeight (F:=K) x y z) := by
  have ha0 : a≠0 := by intro h; simpa [h] using ha
  have hb0 : b≠0 := by intro h; simpa [h] using hb
  have hc0 : c≠0 := by intro h; simpa [h] using hc
  obtain ⟨p,hp,hva,hvb,hvc⟩ := exists_norm_unit_prime a b c ha0 hb0 hc0
  refine ⟨p,hp,?_⟩
  intro x y z
  apply ProductCompatibility.hasProductMaps_of_compatible
  intro xs ys hlen _ _ he
  change edgeProduct xs a (b*(p:K)) (c*(p:K)^2)=
    edgeProduct ys a (b*(p:K)) (c*(p:K)^2) at he
  rw [edgeProduct_eq,edgeProduct_eq] at he
  let s := EdgeCounts.ofPairs xs
  let t := EdgeCounts.ofPairs ys
  have hd : s.occupiedDegree=t.occupiedDegree :=
    EdgeCounts.degree_eq_of_normalized_product s t a b c p hp ha0 hb0 hc0 hva hvb hvc he
  rw [EdgeCounts.normalized_product,EdgeCounts.normalized_product,hd] at he
  have hpk : (p:K)≠0 := by
    intro h
    have hh : (p:ℝ)=0 := by simpa using congrArg ι h
    exact hp.ne_zero (by exact_mod_cast hh)
  have hprod : s.product a b c=t.product a b c := mul_right_cancel₀ (pow_ne_zero _ hpk) he
  have hde : ι a*ι c≠(ι b)^2 := by
    intro h
    exact hdet (ι.injective (by simpa using h))
  have hprodR : s.product (ι a) (ι b) (ι c)=t.product (ι a) (ι b) (ι c) := by
    simpa only [EdgeCounts.product,map_mul,map_pow] using congrArg ι hprod
  have hst : s=t := EdgeCounts.eq_of_degree_product s t (ι a) (ι b) (ι c)
    ha hb hc hde (by simpa [s,t] using hlen) hd hprodR
  change edgeProduct xs x y z=edgeProduct ys x y z
  simp only [edgeProduct_eq]
  exact congrArg (fun u : EdgeCounts => u.product x y z) hst
end PlanarHom.BiasedBinaryProductSeparation
