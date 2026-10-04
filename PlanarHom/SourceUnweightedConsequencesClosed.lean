import PlanarHom.BodyUnconditionalClassification
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Boolean RectangularSourceNormSimulation
theorem lemma111_a {q : ℕ} [Nonempty (Fin q)]
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hs : ∀ i j,L.matrices 0 i j=L.matrices 0 j i)
    (hpos : ∀ i j,0<L.matrices 0 i j) (hdiag : ∀ i,L.matrices 0 i i=1)
    (hinj : Function.Injective (L.matrices 0)) :
    PromisedSharpPHard L.problem ∨
      ∃ d : ℕ,∃ e : Fin q≃Cube d,∃ ρ : Fin d→ℝ,
        (∀ r,0<ρ r ∧ ρ r≠1) ∧ Matrix.reindex e e (L.matrices 0)=tensor ρ := by
  rcases L.lemma82 hunit hs hpos hdiag hinj with hh|⟨d,e,ρ,hr,he,_⟩
  · exact Or.inl hh
  · exact Or.inr ⟨d,e,ρ,hr,he⟩
theorem lemma111_b {x y : ℕ} [Nonempty (Fin x)] [Nonempty (Fin y)]
    (L : RealLanguage (x+y) 1 0) (hunit : ∀ i,L.weights i=1)
    (B : Matrix (Fin x) (Fin y) ℝ) (hB : ∀ i j,0<B i j)
    (hM : L.matrices 0=block B)
    (hrows : ∀ i j,i≠j → ∀ t : ℝ,B i≠t•B j)
    (hcolumns : ∀ i j,i≠j → ∀ t : ℝ,B.transpose i≠t•B.transpose j) :
    PromisedSharpPHard L.problem ∨
      ∃ d : ℕ,∃ eX : Fin x≃Cube d,∃ eY : Fin y≃Cube d,
        ∃ γ : ℝ,∃ ρ : Fin d→ℝ,0<γ ∧ (∀ i,0<ρ i ∧ ρ i≠1) ∧
        ∀ i j,B i j=γ*tensor ρ (eX i) (eY j) := by
  rcases RectangularCoreSourceRigidity.proposition92 L hunit B hB hM hrows hcolumns with
    hh|⟨d,_,_,eX,eY,γ,ρ,hγ,hr,he⟩
  · exact Or.inl hh
  · exact Or.inr ⟨d,eX,eY,γ,ρ,hγ,fun i=>⟨(hr i).1,ne_of_lt (hr i).2⟩,he⟩
theorem lemma111_c {q : ℕ}
    (L : RealLanguage q 1 0) (hunit : ∀ i,L.weights i=1)
    (hpd : (L.matrices 0).PosDef) (hpos : ∀ i j,0<L.matrices 0 i j)
    (hnon : ∃ i j,L.matrices 0 i i≠L.matrices 0 j j) : PromisedSharpPHard L.problem :=
  L.positive_nonconstant_diagonal_hard_of_potts positivePottsFoundation hunit hpd hpos hnon
end PlanarHom.AlgebraicProductInterpolation.RealLanguage
