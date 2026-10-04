import PlanarHom.RealAppendixApproximationEndpoints
import PlanarHom.RealRationalOracleDescent

/-! Explicit prescribed canonical-rational target for the fixed relation-
preserving approximation. The original represented-real oracle is unchanged;
its arbitrary valid replies are passed through the proved rational extractor. -/
noncomputable section
namespace PlanarHom.FixedRealApproximation
open DensePolynomial FixedRealExtension Complexity RepresentedBit
variable {n e q:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

/-- A fixed rational approximation has the stated support, signs and error,
and its canonical algebraic-language answers reduce to the original real
source presentation by an actual charged machine. -/
theorem theoremA4_prescribed_rational
    (basis:Module.Basis (Fin e) (RationalFunction n) K) (φ:K→+*ℝ)
    (M:Matrix (Fin q) (Fin q) K) (hs:∀i j,M i j=M j i) (δ:ℝ) (hδ:0 < δ) :
    ∃N:Matrix (Fin q) (Fin q) ℚ,
      (∀i j,N i j=N j i) ∧ (∀i j,N i j=0 ↔ M i j=0) ∧
      (∀i j,|(N i j:ℝ)-φ (M i j)|<δ) ∧
      (∀i j,Real.sign (N i j:ℝ)=Real.sign (φ (M i j))) ∧
      Nonempty (Reduction (ofCanonical (rationalLanguage N).problem)
        (FixedRealMixedInterpolation.problem basis (fun _:Fin 1=>M)
          (fun l:Fin 0=>l.elim0) (fun _=>1))) := by
  obtain ⟨N,hNs,hNz,hNa,hNsg,⟨r⟩⟩:=theoremA4 basis φ M (fun l:Fin 0=>l.elim0) (fun _=>1) hs δ hδ
  exact ⟨N,hNs,hNz,hNa,hNsg,⟨(rationalOracleDescent basis N).trans r⟩⟩

end PlanarHom.FixedRealApproximation
