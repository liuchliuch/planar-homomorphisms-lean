import PlanarHom.CrossFieldProductClasses
import PlanarHom.EffectiveSpectralTransfer

/-! The genuine polynomial/spectral separating bounds retain their fixed source
field when target monomials are evaluated in a varying real extension field. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.CrossFieldSampleBounds
open Complexity.MixedCode ExponentProductSemantics SourceExponentRepresentatives
open EffectiveProductTransfer SymmetricProductIdentities
variable {K L : Type} [Field K] [Field L] [DecidableEq K] {t : ℕ}

/-- Equality tests in the two fields agree with their actual real embeddings. -/
theorem crossCompatibleAt_iff_map (φ : K →+* ℝ) (ψ : L →+* ℝ)
    (A : Fin t → K) (B : Fin t → L) (m : ℕ) :
    CrossCompatibleAt A B m ↔ ExponentProductTables.CompatibleAt
      (fun i => φ (A i)) (fun i => ψ (B i)) m := by
  constructor
  · intro h xs hxs ys hys hz he
    rw [← FieldProductSampling.map_value, ← FieldProductSampling.map_value] at he
    rw [← FieldProductSampling.map_value] at hz
    rw [← FieldProductSampling.map_value, ← FieldProductSampling.map_value]
    exact congrArg ψ (h xs hxs ys hys (fun he => hz (by rw [he,map_zero])) (φ.injective he))
  · intro h xs hxs ys hys hz he
    apply ψ.injective
    rw [FieldProductSampling.map_value, FieldProductSampling.map_value]
    apply h xs hxs ys hys
    · rw [← FieldProductSampling.map_value]
      exact fun hz' => hz (φ.injective (hz'.trans (map_zero φ).symm))
    · rw [← FieldProductSampling.map_value, ← FieldProductSampling.map_value,he]

theorem crossCompatibleAt_zero (A : Fin t → K) (B : Fin t → L) : CrossCompatibleAt A B 0 := by
  intro xs hxs ys hys _ _
  have hv (zs : List ℕ) (hzs : zs ∈ ExponentVectors.weak t 0) : value B zs = 1 := by
    obtain ⟨hl,hs⟩ := (ExponentVectors.mem_weak t 0 zs).mp hzs
    have he : expand t zs=[] := List.length_eq_zero_iff.mp ((expand_length zs hl).trans hs)
    rw [←expand_product,he]
    rfl
  rw [hv xs hxs,hv ys hys]

variable {K₀ K₁ : IntermediateField ℚ ℝ} {q : ℕ}

/-- Polynomial-source sampling, with an arbitrary real target extension field. -/
theorem polynomial_samples (F : Matrix (Fin q) (Fin q) (Polynomial K₀))
    (B : Matrix (Fin q) (Fin q) K₁) (d n₀ : ℕ)
    (hdegree : ∀ i j, (F i j).natDegree ≤ d)
    (hFsym : ∀ x i j, polynomialRealFamily F x i j = polynomialRealFamily F x j i)
    (hBsym : ∀ i j, B i j = B j i)
    (hidentity : ProductIdentities (polynomialRealFamily F) (fun i j => (B i j : ℝ))) :
    ∀ m, ∃ j < (polynomialCandidateCount q d).eval m,
      CrossCompatibleAt (binaryAlphabet (polynomialFamily F (n₀+j))) (binaryAlphabet B) m := by
  intro m
  by_cases hm : m=0
  · subst m
    exact ⟨0,by simp,crossCompatibleAt_zero _ _⟩
  have hord := ordered_identity_of_upper (polynomialRealFamily F) (fun i j => (B i j : ℝ))
    hFsym (fun i j => congrArg (fun x : K₁ => (x : ℝ)) (hBsym i j)) (hidentity m (by omega))
  obtain ⟨n,hn,hb,hc⟩ := PolynomialProductZeros.exists_compatible_sample
    (fun e : Fin (q*q) => (F (finProdFinEquiv.symm e).1 (finProdFinEquiv.symm e).2).map K₀.val.toRingHom)
    (binaryAlphabet (fun i j => (B i j : ℝ))) d m n₀
    (fun e => Polynomial.natDegree_map_le.trans (hdegree _ _)) hord
  refine ⟨n-n₀, ?_, ?_⟩
  · rw [polynomialCandidateCount_eval]
    omega
  · have he : n₀+(n-n₀)=n := by omega
    rw [he]
    apply (crossCompatibleAt_iff_map K₀.val.toRingHom K₁.val.toRingHom _ _ m).mpr
    convert hc using 1
    funext e
    exact polynomialFamily_coe F n _ _

/-- Spectral-source sampling, independent of the target field presentation. -/
theorem spectral_samples (A : Matrix (Fin q) (Fin q) K₀) (B : Matrix (Fin q) (Fin q) K₁)
    (hA : (SpectralFieldPresentation.realMatrix A).PosDef) (n₀ : ℕ)
    (hBsym : ∀ i j, B i j = B j i)
    (hidentity : ProductIdentities (matrixPowerRealFamily A) (fun i j => (B i j : ℝ))) :
    ∀ m, ∃ j < (spectralCandidateCount q
      (Nat.card (spectrum ℝ (SpectralFieldPresentation.realMatrix A)))).eval m,
      CrossCompatibleAt (binaryAlphabet (A ^ (n₀+j))) (binaryAlphabet B) m := by
  intro m
  by_cases hm : m=0
  · subst m
    exact ⟨0,by simp,crossCompatibleAt_zero _ _⟩
  have hord := ordered_identity_of_upper (matrixPowerRealFamily A) (fun i j => (B i j : ℝ))
    (matrixPowerRealFamily_symm A) (fun i j => congrArg (fun x : K₁ => (x : ℝ)) (hBsym i j))
    (hidentity m (by omega))
  obtain ⟨n,hn,hb,hc⟩ := SpectralProductZeros.matrixPower_exists_compatible_sample
    (SpectralFieldPresentation.realMatrix A) (fun i j => (B i j : ℝ)) hA m n₀ hord
  refine ⟨n-n₀, ?_, ?_⟩
  · rw [spectralCandidateCount_eval]
    omega
  · have he : n₀+(n-n₀)=n := by omega
    rw [he]
    apply (crossCompatibleAt_iff_map K₀.val.toRingHom K₁.val.toRingHom _ _ m).mpr
    convert hc using 1
    funext e
    exact matrixPowerFamily_coe A hA.1 n _ _

end PlanarHom.CrossFieldSampleBounds
