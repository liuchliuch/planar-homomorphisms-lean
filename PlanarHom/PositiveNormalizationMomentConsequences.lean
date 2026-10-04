import PlanarHom.PositiveNormalizationSourcePrograms
import PlanarHom.PositiveClassMomentFieldRigidity
import PlanarHom.FiniteFieldQuotientLanguage

/-! NEW actual normalization-moment consequences. Every exponent has a genuine
original-source program, and moment constancy is proved on the actual numerical
row quotient before transporting to the fixed real quotient. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode PositiveClassMomentRigidity
variable {q bt ut : ℕ} [Nonempty (Fin q)]

theorem normalized_weighted_moments_constant (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hp : ∀i j,0<L.matrices old i j) (hw : ∀i,0<L.weights i)
    (hnot : ¬PromisedSharpPHard L.problem) (m : ℕ)
    (r s : Quotient (Twins.rowSetoid (diagonalNormalize (L.matrices old)))) :
    Twins.quotientWeight (diagonalNormalize (L.matrices old))
      (fun i=>L.weights i*(L.matrices old i i)^m) r =
    Twins.quotientWeight (diagonalNormalize (L.matrices old))
      (fun i=>L.weights i*(L.matrices old i i)^m) s := by
  obtain ⟨F,h₀,n,bF,C,hC,hr⟩ := PositiveNormalizationSourcePrograms.exists_normalized_moment_sources
    L.basis L.matricesK L.unariesK L.weightsK old (fun i=>hp i i)
  change ∀i j,(C i j:ℝ)=diagonalNormalize (L.matrices old) i j at hC
  have hsC : ∀i j,C i j=C j i := by
    intro i j
    apply Subtype.ext
    rw [hC,hC]
    exact diagonalNormalize_symmetric _ hs i j
  have hpC : ∀i j,0<(C i j:ℝ) := by
    intro i j
    rw [hC]
    exact diagonalNormalize_positive _ hp i j
  have hdC : ∀i,C i i=1 := by
    intro i
    apply Subtype.ext
    rw [hC]
    exact diagonalNormalize_diagonal _ (fun i=>hp i i) i
  let wm : Fin q → F := fun i=>IntermediateField.inclusion h₀ (L.weightsK i) *
    (IntermediateField.inclusion h₀ (L.matricesK old i i))^m
  have hwreal : ∀i,(wm i:ℝ)=L.weights i*(L.matrices old i i)^m := by
    intro i
    simp only [wm,IntermediateField.coe_mul,IntermediateField.coe_pow]
    rfl
  letI : Nonempty (Quotient (Twins.rowSetoid C)) := ⟨Quotient.mk _ (Classical.arbitrary (Fin q))⟩
  letI : IsStrictOrderedRing F := Subfield.toIsStrictOrderedRing F.toSubfield
  have hpQ : ∀i j,0<(Twins.quotientMatrix C hsC i j:ℝ) := by
    intro i j
    induction i using Quotient.inductionOn with
    | h i =>
      induction j using Quotient.inductionOn with
      | h j => exact hpC i j
  have hdQ : ∀i,Twins.quotientMatrix C hsC i i=1 := by
    intro i
    induction i using Quotient.inductionOn with
    | h i => exact hdC i
  have hwm : ∀i,0<wm i := by
    intro i
    change 0<(wm i:ℝ)
    rw [hwreal]
    exact mul_pos (hw i) (pow_pos (hp i i) _)
  have hwQ : ∀i,0<((Twins.quotientWeight C wm i:F):ℝ) :=
    fun i=>Twins.quotientWeight_pos C wm hwm i
  obtain ⟨rm⟩ := hr m
  have available := (ActualTwins.quotientReduction bF C hsC wm).trans rm
  have hconstant := field_weights_constant_of_available hPotts bF (Twins.quotientMatrix C hsC)
    (Twins.quotientWeight C wm) (Twins.quotientMatrix_symmetric C hsC) hpQ hdQ
    (Twins.quotientMatrix_rows_injective C hsC) hwQ L.problem available hnot
  let er := FiniteFieldQuotientLanguage.realQuotientEquiv C (diagonalNormalize (L.matrices old)) hC
  have h := congrArg (fun z:F=>(z:ℝ)) (hconstant (er.symm r) (er.symm s))
  dsimp only at h
  rw [FiniteFieldQuotientLanguage.quotientWeight_real C _ hC wm,
    FiniteFieldQuotientLanguage.quotientWeight_real C _ hC wm] at h
  change Twins.quotientWeight _ (fun i=>(wm i:ℝ)) (er (er.symm r)) =
    Twins.quotientWeight _ (fun i=>(wm i:ℝ)) (er (er.symm s)) at h
  simpa only [er.apply_symm_apply,hwreal] using h

theorem normalized_moments_constant (hPotts : PositivePottsFoundation)
    (L : RealLanguage q bt ut) (old : Fin bt)
    (hs : ∀i j,L.matrices old i j=L.matrices old j i)
    (hp : ∀i j,0<L.matrices old i j) (hunit : ∀i,L.weights i=1)
    (hnot : ¬PromisedSharpPHard L.problem) (m : ℕ)
    (r s : Quotient (Twins.rowSetoid (diagonalNormalize (L.matrices old)))) :
    Twins.quotientWeight (diagonalNormalize (L.matrices old)) (fun i=>(L.matrices old i i)^m) r =
    Twins.quotientWeight (diagonalNormalize (L.matrices old)) (fun i=>(L.matrices old i i)^m) s := by
  have hw : ∀i,0<L.weights i := fun i=>by rw [hunit]; exact zero_lt_one
  simpa only [hunit,one_mul] using L.normalized_weighted_moments_constant hPotts old hs hp hw hnot m r s

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
