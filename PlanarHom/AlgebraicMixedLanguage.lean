import PlanarHom.FixedAlgebraicField
import PlanarHom.PositiveUnaryPowerField
import PlanarHom.MixedEvaluationFieldMap

/-! A single actual finite field for all fixed real-algebraic mixed constraints,
including a fixed finite auxiliary collection. No field depends on input graphs. -/
noncomputable section
namespace PlanarHom.AlgebraicMixedLanguage
open FixedAlgebraicField
variable {C I : Type} [Fintype C] [Fintype I] {bt ut : ℕ}

def alphabet (M : Fin bt → Matrix C C ℝ) (U : Fin ut → C → ℝ) (w : C → ℝ) (extra : I → ℝ) :
    ((Fin bt × C × C) ⊕ ((Fin ut × C) ⊕ (C ⊕ I))) → ℝ :=
  Sum.elim (fun p => M p.1 p.2.1 p.2.2)
    (Sum.elim (fun p => U p.1 p.2) (Sum.elim w extra))

omit [Fintype C] [Fintype I] in
theorem alphabet_isAlgebraic (M : Fin bt → Matrix C C ℝ) (U : Fin ut → C → ℝ)
    (w : C → ℝ) (extra : I → ℝ)
    (hM : ∀ l i j, IsAlgebraic ℚ (M l i j)) (hU : ∀ l i, IsAlgebraic ℚ (U l i))
    (hw : ∀ i, IsAlgebraic ℚ (w i)) (he : ∀ i, IsAlgebraic ℚ (extra i)) :
    ∀ i, IsAlgebraic ℚ (alphabet M U w extra i) := by
  intro i
  rcases i with p | p
  · exact hM p.1 p.2.1 p.2.2
  · rcases p with p | p
    · exact hU p.1 p.2
    · rcases p with p | p
      · exact hw p
      · exact he p

/-- A fixed common field contains every original entry, background value and
all entries in any finite auxiliary collection simultaneously. -/
theorem exists_common_field (M : Fin bt → Matrix C C ℝ) (U : Fin ut → C → ℝ)
    (w : C → ℝ) (extra : I → ℝ)
    (hM : ∀ l i j, IsAlgebraic ℚ (M l i j)) (hU : ∀ l i, IsAlgebraic ℚ (U l i))
    (hw : ∀ i, IsAlgebraic ℚ (w i)) (he : ∀ i, IsAlgebraic ℚ (extra i)) :
    ∃ F : IntermediateField ℚ ℝ, FiniteDimensional ℚ F ∧
      (∀ l i j, M l i j ∈ F) ∧ (∀ l i, U l i ∈ F) ∧
      (∀ i, w i ∈ F) ∧ (∀ i, extra i ∈ F) := by
  refine ⟨commonField (alphabet M U w extra),
    commonField_finiteDimensional _ (alphabet_isAlgebraic M U w extra hM hU hw he), ?_, ?_, ?_, ?_⟩
  · intro l i j
    exact mem_commonField (alphabet M U w extra) (.inl (l,i,j))
  · intro l i
    exact mem_commonField (alphabet M U w extra) (.inr (.inl (l,i)))
  · intro i
    exact mem_commonField (alphabet M U w extra) (.inr (.inr (.inl i)))
  · intro i
    exact mem_commonField (alphabet M U w extra) (.inr (.inr (.inr i)))

/-- The source product-map hypothesis descends to literal subfield entries. -/
theorem hasProductMaps_lift {J : Type} (F : IntermediateField ℚ ℝ)
    (A B : J → F)
    (h : ProductCompatibility.HasProductMaps (fun i => (A i : ℝ)) (fun i => (B i : ℝ))) :
    ProductCompatibility.HasProductMaps A B := by
  apply ProductCompatibility.hasProductMaps_of_compatible
  apply ProductCompatibility.compatible_of_field_embedding F.val.toRingHom
  exact ProductCompatibility.compatible_of_hasProductMaps _ _ h

end PlanarHom.AlgebraicMixedLanguage
