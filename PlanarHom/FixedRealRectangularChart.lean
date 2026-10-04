import PlanarHom.RectangularBooleanCore
import PlanarHom.FixedRealNonproportionalClass
import PlanarHom.FixedRealLemmaA11

/-! NEW source-field realization of the rectangular Boolean chart. Scale and
all tensor parameters are ratios of literal source entries. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealRectangularRigidity
open DensePolynomial Complexity RepresentedBit Boolean
variable {n e : ℕ} {K X Y : Type} [Field K]
    [Algebra (RationalFunction n) K] [Algebra K ℝ]
    [Fintype X] [Fintype Y]

def double (R : Matrix X Y K) : Matrix (X ⊕ Y) (X ⊕ Y) K :=
  Matrix.fromBlocks 0 R R.transpose 0

def realR (R : Matrix X Y K) : Matrix X Y ℝ := fun x y => algebraMap K ℝ (R x y)

def problem (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (R : Matrix X Y K) (μ : X → K) (ν : Y → K) : Problem :=
  FixedRealComponents.problem basis (fun _ : Fin 1 => double R)
    (fun l : Fin 0 => l.elim0) (Sum.elim μ ν)

theorem double_real (R : Matrix X Y K) :
    (fun i j => algebraMap K ℝ (double R i j)) = BipartiteFullTwins.double (realR R) := by
  funext i j
  cases i <;> cases j <;> simp [double, realR, BipartiteFullTwins.double]

theorem real_class_of_not_hard [Nonempty X] [Nonempty Y]
    (basis : Module.Basis (Fin e) (RationalFunction n) K)
    (R : Matrix X Y K) (μ : X → K) (ν : Y → K)
    (hp : ∀ x y, 0 < realR R x y)
    (hrows : ∀ x x', x ≠ x' → ∀ t : ℝ, realR R x ≠ t • realR R x')
    (hcols : ∀ y y', y ≠ y' → ∀ t : ℝ, (realR R).transpose y ≠ t • (realR R).transpose y')
    (hμ : ∀ x, 0 < algebraMap K ℝ (μ x))
    (hν : ∀ y, 0 < algebraMap K ℝ (ν y))
    (hn : ¬SharpPHard (problem basis R μ ν)) :
    Structures.NonnegativeClass (BipartiteFullTwins.double (realR R)) := by
  have hs : ∀ i j, double R i j = double R j i := by
    intro i j
    cases i <;> cases j <;> rfl
  have hnn : ∀ i j, 0 ≤ algebraMap K ℝ (double R i j) := by
    intro i j
    cases i with
    | inl x => cases j with
      | inl x' => simp [double]
      | inr y => exact (hp x y).le
    | inr y => cases j with
      | inl x => exact (hp x y).le
      | inr y' => simp [double]
  have hw : ∀ i, 0 < algebraMap K ℝ (Sum.elim μ ν i) := by
    intro i
    cases i with
    | inl x => exact hμ x
    | inr y => exact hν y
  have hz : ∀ i, (fun j => algebraMap K ℝ (double R i j)) ≠ 0 := by
    intro i
    rw [congrFun (double_real R) i]
    exact RectangularUnitCoreSource.double_rows_nonzero (realR R) hp i
  have hproj : ∀ i j, i ≠ j → ∀ t : ℝ,
      (fun k => algebraMap K ℝ (double R i k)) ≠
        t • (fun k => algebraMap K ℝ (double R j k)) := by
    intro i j hij t
    rw [congrFun (double_real R) i, congrFun (double_real R) j]
    exact RectangularBooleanCore.double_nonproportional (realR R) hp hrows hcols i j hij t
  have hc := FixedRealNonproportionalClass.finite_class_of_not_hard basis
    (double R) (Sum.elim μ ν) hs hnn hw hz hproj hn
  rwa [double_real] at hc

theorem source_entry_ratios {d : ℕ} (R : Matrix X Y K)
    (eX : X ≃ Cube d) (eY : Y ≃ Cube d) (γ : ℝ) (ρ : Fin d → ℝ)
    (hγ : 0 < γ)
    (hm : ∀ x y, realR R x y = γ * Boolean.tensor ρ (eX x) (eY y)) :
    ∃ c : K, ∃ p : Fin d → K,
      algebraMap K ℝ c = γ ∧ (∀ r, algebraMap K ℝ (p r) = ρ r) ∧
      ∀ x y, R x y = c * FixedRealTensorCoreEasy.tensor p (eX x) (eY y) := by
  let z : Cube d := fun _ => false
  let c := R (eX.symm z) (eY.symm z)
  let p : Fin d → K := fun r => R (eX.symm z) (eY.symm (unitBit r)) / c
  have hc : algebraMap K ℝ c = γ := by
    simpa only [c, realR, eX.apply_symm_apply, eY.apply_symm_apply,
      tensor_diag, mul_one] using hm (eX.symm z) (eY.symm z)
  have hp (r : Fin d) : algebraMap K ℝ (p r) = ρ r := by
    change algebraMap K ℝ (R (eX.symm z) (eY.symm (unitBit r)) / c) = _
    rw [map_div₀, hc]
    change realR R (eX.symm z) (eY.symm (unitBit r)) / γ = _
    rw [hm, eX.apply_symm_apply, eY.apply_symm_apply]
    simp only [z, tensor_unitBit]
    field_simp [ne_of_gt hγ]
  refine ⟨c, p, hc, hp, ?_⟩
  intro x y
  apply (algebraMap K ℝ).injective
  rw [map_mul, hc, FixedRealLemmaA10.tensor_real]
  simpa only [hp] using hm x y

theorem chart_of_not_hard [Nonempty X] [Nonempty Y]
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
      ∀ x y, R x y = c * FixedRealTensorCoreEasy.tensor ρ (eX x) (eY y) := by
  have hclass := real_class_of_not_hard basis R μ ν hp hrows hcols hμ hν hn
  obtain ⟨d, eX, eY, γ, p, hγ, hp', hm⟩ :=
    RectangularBooleanCore.tensor_core_of_nonnegativeClass (realR R) hp hrows hcols hclass
  obtain ⟨c, ρ, hc, hρ, hR⟩ := source_entry_ratios R eX eY γ p hγ hm
  exact ⟨d, eX, eY, c, ρ, hc.symm ▸ hγ, fun r => (hρ r).symm ▸ hp' r, hR⟩

end PlanarHom.FixedRealRectangularRigidity
