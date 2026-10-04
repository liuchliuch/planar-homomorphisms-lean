import PlanarHom.FixedRealRectangularChart

/-! NEW field-level A.11 rigidity for the original rectangular weighted source.
The actual color-reindexing reduction transfers either nonconstant side to
the checked A.11 hard endpoint, with no external-field output assumption. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealRectangularRigidity
open DensePolynomial Complexity RepresentedBit Boolean
variable {n e : ℕ} {K X Y : Type} [Field K]
    [Algebra (RationalFunction n) K] [Algebra K ℝ]
    [Fintype X] [Fintype Y]

theorem weights_constant_of_chart {d : ℕ}
    (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (R : Matrix X Y K) (μ : X → K) (ν : Y → K)
    (eX : X ≃ Cube d) (eY : Y ≃ Cube d) (c : K) (ρ : Fin d → K)
    (hc : 0 < algebraMap K ℝ c)
    (hρ : ∀ r, 0 < algebraMap K ℝ (ρ r) ∧ algebraMap K ℝ (ρ r) ≠ 1)
    (hR : ∀ x y, R x y = c * FixedRealTensorCoreEasy.tensor ρ (eX x) (eY y))
    (hμ : ∀ x, 0 < algebraMap K ℝ (μ x))
    (hν : ∀ y, 0 < algebraMap K ℝ (ν y))
    (hn : ¬SharpPHard (problem basis R μ ν)) :
    (∀ x x', μ x = μ x') ∧ (∀ y y', ν y = ν y') := by
  let u : Cube d → K := fun x => μ (eX.symm x)
  let v : Cube d → K := fun y => ν (eY.symm y)
  let a : (Cube d ⊕ Cube d) ≃ (X ⊕ Y) := Equiv.sumCongr eX.symm eY.symm
  have red := FixedRealActualTwins.reindexReduction basis (double R) (Sum.elim μ ν) a
  have he : (fun i j => double R (a i) (a j)) =
      FixedRealBipartiteLeftHard.double (c • FixedRealTensorCoreEasy.tensor ρ) := by
    funext i j
    cases i <;> cases j <;>
      simp [a, double, FixedRealBipartiteLeftHard.double, hR]
  have hw : (fun i => Sum.elim μ ν (a i)) = Sum.elim u v := by
    funext i
    cases i <;> rfl
  rw [he, hw] at red
  have hnot : ¬SharpPHard (FixedRealLemmaA11.problem basis c ρ u v) :=
    fun hh => hn (hh.trans red)
  have hu : ∀ x, 0 < algebraMap K ℝ (u x) := fun x => hμ (eX.symm x)
  have hv : ∀ y, 0 < algebraMap K ℝ (v y) := fun y => hν (eY.symm y)
  constructor
  · intro x x'
    by_contra hxx
    apply hnot
    apply FixedRealLemmaA11.nonconstant_hard basis c hc ρ
      (fun r => (hρ r).1) (fun r => (hρ r).2) u v hu hv
    exact Or.inl ⟨eX x, eX x', by simpa only [u, eX.symm_apply_apply] using hxx⟩
  · intro y y'
    by_contra hyy
    apply hnot
    apply FixedRealLemmaA11.nonconstant_hard basis c hc ρ
      (fun r => (hρ r).1) (fun r => (hρ r).2) u v hu hv
    exact Or.inr ⟨eY y, eY y', by simpa only [v, eY.symm_apply_apply] using hyy⟩

/-- Complete rectangular core rigidity in the prescribed original field.
The two resulting side constants may be different. -/
theorem rigidity_of_not_hard [Nonempty X] [Nonempty Y]
    (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (R : Matrix X Y K) (μ : X → K) (ν : Y → K)
    (hp : ∀ x y, 0 < realR R x y)
    (hrows : ∀ x x', x ≠ x' → ∀ t : ℝ, realR R x ≠ t • realR R x')
    (hcols : ∀ y y', y ≠ y' → ∀ t : ℝ, (realR R).transpose y ≠ t • (realR R).transpose y')
    (hμ : ∀ x, 0 < algebraMap K ℝ (μ x))
    (hν : ∀ y, 0 < algebraMap K ℝ (ν y))
    (hn : ¬SharpPHard (problem basis R μ ν)) :
    ∃ d, ∃ eX : X ≃ Cube d, ∃ eY : Y ≃ Cube d,
      ∃ c : K, ∃ ρ : Fin d → K,
      0 < algebraMap K ℝ c ∧
      (∀ r, 0 < algebraMap K ℝ (ρ r) ∧ algebraMap K ℝ (ρ r) ≠ 1) ∧
      (∀ x y, R x y = c * FixedRealTensorCoreEasy.tensor ρ (eX x) (eY y)) ∧
      (∀ x x', μ x = μ x') ∧ (∀ y y', ν y = ν y') := by
  obtain ⟨d, eX, eY, c, ρ, hc, hρ, hR⟩ :=
    chart_of_not_hard basis R μ ν hp hrows hcols hμ hν hn
  exact ⟨d, eX, eY, c, ρ, hc, hρ, hR,
    weights_constant_of_chart basis R μ ν eX eY c ρ hc hρ hR hμ hν hn⟩

end PlanarHom.FixedRealRectangularRigidity
