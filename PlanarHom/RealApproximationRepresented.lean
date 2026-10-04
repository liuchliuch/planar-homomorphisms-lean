import PlanarHom.RealApproximationProductCompatibility
import PlanarHom.FixedRealJointInterpolation

/-! NEW: exact represented joint availability of rational approximants. The
output field is a prescribed fixed finite extension of Q(X), equipped with an
explicit real embedding. No number-field codec is assigned to arbitrary reals. -/
noncomputable section
open Classical
namespace PlanarHom.ProductCompatibility
variable {I K L : Type} [Field K] [Field L]

theorem Compatible.of_injective_map (φ : K →+* L) {A B : I → K}
    (h : Compatible (fun i => φ (A i)) (fun i => φ (B i))) : Compatible A B := by
  intro xs ys hl hx hy he
  apply φ.injective
  simp only [map_list_prod, List.map_map]
  exact h xs ys hl (fun i hi => (map_ne_zero φ).mpr (hx i hi))
    (fun i hi => (map_ne_zero φ).mpr (hy i hi))
    (by simpa only [map_list_prod,List.map_map] using congrArg φ he)

end PlanarHom.ProductCompatibility
namespace PlanarHom.FixedRealApproximation
open DensePolynomial FixedRealExtension RepresentedBit ProductCompatibility FiniteLanguageAliases
variable {n e q b u : ℕ} {K : Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis : Module.Basis (Fin e) (RationalFunction n) K) (φ : K →+* ℝ)

/-- A.4 as an exact common-field oracle reduction, retaining every old binary
and unary label and any fixed background weights. Symmetry, support and signs
are retained by the chosen rational matrices. -/
theorem theoremA4_joint (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin u → Fin q → K) (w : Fin q → K)
    (hs : ∀l i j, M l i j = M l j i) (δ : ℝ) (hδ : 0 < δ)
    (base : Problem) (available : Reduction (FixedRealMixedInterpolation.problem basis M U w) base) :
    ∃N : Fin b → Matrix (Fin q) (Fin q) ℚ,
      (∀l i j, N l i j = N l j i) ∧
      (∀l i j, N l i j = 0 ↔ M l i j = 0) ∧
      (∀l i j, |(N l i j : ℝ) - φ (M l i j)| < δ) ∧
      (∀l i j, Real.sign (N l i j : ℝ) = Real.sign (φ (M l i j))) ∧
      Nonempty (Reduction
        (FixedRealMixedInterpolation.problem basis
          (appendFamily M (fun l i j => (N l i j : K))) U w) base) := by
  let A : Fin b × Fin q × Fin q → ℝ := fun z => φ (M z.1 z.2.1 z.2.2)
  obtain ⟨r,hz,ha,hsg,hc⟩ := RelationApproximation.rational_approximation_with_zeros A δ hδ
  let N : Fin b → Matrix (Fin q) (Fin q) ℚ := fun l i j => r (l,i,j)
  have hz' : ∀z, A z = 0 → (r z : ℝ) = 0 := by
    intro z h
    exact_mod_cast (hz z).mpr h
  have hnz : ∀l i j, N l i j = 0 ↔ M l i j = 0 := by
    intro l i j
    simpa [N,A] using hz (l,i,j)
  refine ⟨N,?_,hnz,fun l i j => ha (l,i,j),fun l i j => hsg (l,i,j),?_⟩
  · intro l i j
    apply Rat.cast_injective (α := ℝ)
    exact RelationApproximation.equal_entries_of_compatible hz' hc (by simp [A,hs l i j])
  · have hmaps (l : Fin b) : HasProductMaps (fun p : Fin q × Fin q => M l p.1 p.2)
        (fun p => (N l p.1 p.2 : K)) := by
      apply hasProductMaps_of_compatible
      apply Compatible.of_injective_map φ
      have hh := hc.comp (fun p : Fin q × Fin q => (l,p))
      simpa only [Function.comp_def,A,N,map_ratCast] using hh
    exact ⟨FixedRealMixedInterpolation.binaryFinite_joint basis M U w
      (fun l i j => (N l i j : K)) id
      (fun l i j h => by simp [(hnz l i j).mpr h]) hmaps base available⟩

end PlanarHom.FixedRealApproximation
