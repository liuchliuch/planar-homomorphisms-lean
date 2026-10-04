import PlanarHom.FixedRealPresentationFiniteness
import PlanarHom.FixedSubfieldPresentationExistence
import PlanarHom.FixedRealIntegerExtraction

/-! NEW: actual finite relative transcendence data for any prescribed field
embedding and any fixed RF-basis ambient presentation. No field-presentation
search is part of the input-dependent program. -/
noncomputable section
open Classical
namespace PlanarHom.FixedSubfieldRepresentationChoices
open DensePolynomial

theorem finite_over_family {F K ι : Type*} [Field F] [Field K] [Algebra F K]
    (hfg : (⊤ : IntermediateField F K).FG) (y : ι → K) (hy : IsTranscendenceBasis F y) :
    FiniteDimensional (IntermediateField.adjoin F (Set.range y)) K := by
  obtain ⟨S,hS⟩ := hfg
  let B := IntermediateField.adjoin F (Set.range y)
  letI : Algebra.IsAlgebraic B K := hy.isAlgebraic_field
  letI : FiniteDimensional B (IntermediateField.adjoin B (S : Set K)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have htop : IntermediateField.adjoin B (S : Set K) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top F hS
  haveI : FiniteDimensional B (⊤ : IntermediateField B K) := htop ▸ inferInstance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem sourceCharZero (d : ℕ) (K : Type) [Field K] [Algebra (RationalFunction d) K] : CharZero K :=
  (RingHom.charZero_iff
    (ϕ := (algebraMap (RationalFunction d) K).comp (DenseRationalConstantExtraction.constantMap d))
    ((algebraMap (RationalFunction d) K).comp (DenseRationalConstantExtraction.constantMap d)).injective).mp inferInstance

theorem exists_relative_family {d e : ℕ} {K F : Type} [Field K] [Field F]
    [Algebra (RationalFunction d) K]
    (source : Module.Basis (Fin e) (RationalFunction d) K) (embed : F →+* K) :
    letI : Algebra F K := embed.toAlgebra
    ∃ b : ℕ, ∃ y : Fin b → K, IsTranscendenceBasis F y ∧
      FiniteDimensional (IntermediateField.adjoin F (Set.range y)) K := by
  letI : Algebra F K := embed.toAlgebra
  letI : CharZero K := sourceCharZero d K
  letI : CharZero F := embed.charZero
  letI : Algebra ℚ K := (Rat.castHom K).toAlgebra
  letI : Algebra ℚ F := (Rat.castHom F).toAlgebra
  letI : IsScalarTower ℚ F K := IsScalarTower.of_algebraMap_eq (fun q =>
    RingHom.congr_fun (RingHom.ext_rat (algebraMap ℚ K)
      ((algebraMap F K).comp (algebraMap ℚ F))) q)
  have hfg : (⊤ : IntermediateField F K).FG := by
    apply IntermediateField.FG.of_restrictScalars (K := ℚ)
    simpa using FixedRealPresentationFiniteness.top_fg source
  obtain ⟨Y,hfin,hY,hfd⟩ := FixedSubfieldPresentation.exists_finite_relative_basis hfg
  letI : Fintype Y := hfin.fintype
  let y : Fin (Fintype.card Y) → K := fun i => ((Fintype.equivFin Y).symm i).val
  have hy : IsTranscendenceBasis F y := hY.comp_equiv (Fintype.equivFin Y).symm
  exact ⟨Fintype.card Y,y,hy,finite_over_family hfg y hy⟩

end PlanarHom.FixedSubfieldRepresentationChoices
