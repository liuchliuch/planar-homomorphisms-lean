import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.FieldTheory.Perfect
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-! NEW: the compatible relative transcendence basis and finite algebraic
presentation exist for a fixed finitely generated field and a prescribed
subfield. These are mathematical constant choices, not runtime basis oracles. -/
noncomputable section
open Classical
open scoped IntermediateField.algebraAdjoinAdjoin
namespace PlanarHom.FixedSubfieldPresentation
variable {K E : Type*} [Field K] [Field E] [Algebra K E]

theorem algebraic_over_generator_ring {S : Set E}
    (hS : IntermediateField.adjoin K S = ⊤) : Algebra.IsAlgebraic (Algebra.adjoin K S) E := by
  constructor
  intro x
  have hx : x ∈ IntermediateField.adjoin K S := by rw [hS]; trivial
  have ha := Algebra.IsAlgebraic.isAlgebraic
    (R := Algebra.adjoin K S) (⟨x,hx⟩ : IntermediateField.adjoin K S)
  exact ha.algHom (IsScalarTower.toAlgHom (Algebra.adjoin K S) (IntermediateField.adjoin K S) E)

theorem finite_over_relative_basis (hfg : (⊤ : IntermediateField K E).FG)
    {Y : Set E} (hY : IsTranscendenceBasis K ((↑) : Y → E)) :
    FiniteDimensional (IntermediateField.adjoin K Y) E := by
  obtain ⟨S,hS⟩ := hfg
  let B := IntermediateField.adjoin K Y
  have hY' : Algebra.IsAlgebraic B E := by
    have hr : Set.range ((↑) : Y → E) = Y := by ext x; simp
    change Algebra.IsAlgebraic (IntermediateField.adjoin K Y) E
    rw [← hr]
    exact hY.isAlgebraic_field
  letI : Algebra.IsAlgebraic B E := hY'
  letI : FiniteDimensional B (IntermediateField.adjoin B (S : Set E)) :=
    IntermediateField.finiteDimensional_adjoin (fun x _ => (Algebra.IsAlgebraic.isAlgebraic x).isIntegral)
  have htop : IntermediateField.adjoin B (S : Set E) = ⊤ :=
    IntermediateField.adjoin_eq_top_of_adjoin_eq_top K hS
  haveI : FiniteDimensional B (⊤ : IntermediateField B E) := htop ▸ inferInstance
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

theorem exists_finite_relative_basis (hfg : (⊤ : IntermediateField K E).FG) :
    ∃ Y : Set E, Y.Finite ∧ IsTranscendenceBasis K ((↑) : Y → E) ∧
      FiniteDimensional (IntermediateField.adjoin K Y) E := by
  obtain ⟨S,hS⟩ := hfg
  letI := algebraic_over_generator_ring hS
  obtain ⟨Y,hYS,hY⟩ := exists_isTranscendenceBasis_subset (R := K) (S : Set E)
  exact ⟨Y,S.finite_toSet.subset hYS,hY,finite_over_relative_basis ⟨S,hS⟩ hY⟩

theorem exists_relative_power_basis [CharZero K]
    (hfg : (⊤ : IntermediateField K E).FG) :
    ∃ Y : Set E, Y.Finite ∧ IsTranscendenceBasis K ((↑) : Y → E) ∧
      Nonempty (PowerBasis (IntermediateField.adjoin K Y) E) := by
  obtain ⟨Y,hfin,hY,hfd⟩ := exists_finite_relative_basis hfg
  letI := hfd
  letI : CharZero (IntermediateField.adjoin K Y) := Algebra.charZero_of_charZero K _
  exact ⟨Y,hfin,hY,⟨Field.powerBasisOfFiniteOfSeparable _ _⟩⟩

/-- Finiteness of the ambient field's generators over Q supplies the relative
finite generation over every prescribed intermediate field. -/
theorem prescribed_subfield_relative_presentation {F : Type*} [Field F] [Algebra ℚ F]
    (hF : (⊤ : IntermediateField ℚ F).FG) (F₀ : IntermediateField ℚ F) :
    ∃ Y : Set F, Y.Finite ∧ IsTranscendenceBasis F₀ ((↑) : Y → F) ∧
      Nonempty (PowerBasis (IntermediateField.adjoin F₀ Y) F) := by
  letI : CharZero F₀ := Algebra.charZero_of_charZero ℚ _
  have hrel : (⊤ : IntermediateField F₀ F).FG := by
    apply IntermediateField.FG.of_restrictScalars (K := ℚ)
    simpa using hF
  exact exists_relative_power_basis hrel

end PlanarHom.FixedSubfieldPresentation
