import PlanarHom.PositiveUnaryPowerOverfield
import PlanarHom.DomainProductInterpolationReductions
import PlanarHom.FieldPresentationReductions

/-!
# Actual positive-unary rational-power replacement reductions

The target unary is the genuine real rational power in a fixed finite overfield.
Product compatibility is derived from positivity and real-power identities.
Actual interpolation machines are composed with actual fixed-field answer
conversion, preserving the original source oracle's chosen output basis.
The fixed-slot statements below are the replacement stage of joint availability;
appended-label wrappers retain a separate original unary label.
-/

noncomputable section
open Classical
namespace PlanarHom.PositiveUnaryRationalPowers
open ProductCompatibility Complexity Complexity.MixedCode
variable {I : Type} {K₀ K : IntermediateField ℚ ℝ}

/-- Literal real-power values inside an overfield satisfy the machine theorem's
product-map premise; it is not supplied as a new assumption. -/
theorem lifted_power_hasProductMaps (h₀ : K₀ ≤ K) (u : I → K₀) (v : I → K)
    (hpos : ∀ i, 0 < (u i : ℝ)) (r : ℚ)
    (hv : ∀ i, (v i : ℝ) = (u i : ℝ) ^ (r : ℝ)) :
    HasProductMaps (fun i => IntermediateField.inclusion h₀ (u i)) v := by
  apply hasProductMaps_of_compatible
  apply compatible_of_field_embedding K.val.toRingHom
  change Compatible (fun i => (u i : ℝ)) (fun i => (v i : ℝ))
  simp_rw [hv]
  exact compatible_real_rpow (fun i => (u i : ℝ)) hpos r

/-- Positivity discharges the source-zero requirement even for nonpositive exponents. -/
theorem lifted_power_zero (h₀ : K₀ ≤ K) (u : I → K₀) (v : I → K)
    (hpos : ∀ i, 0 < (u i : ℝ)) :
    ∀ i, IntermediateField.inclusion h₀ (u i) = 0 → v i = 0 := by
  intro i hi
  have hz : (u i : ℝ) = 0 := congrArg (fun x : K => (x : ℝ)) hi
  exact ((ne_of_gt (hpos i)) hz).elim

/-- Map the unchanged unary language and replace just one named slot. -/
def powerReplacement {ut : ℕ} (h₀ : K₀ ≤ K) (U : Fin ut → I → K₀)
    (selected : Fin ut) (v : I → K) : Fin ut → I → K :=
  Function.update (fun l i => IntermediateField.inclusion h₀ (U l i)) selected v

@[simp] theorem powerReplacement_selected {ut : ℕ} (h₀ : K₀ ≤ K)
    (U : Fin ut → I → K₀) (selected : Fin ut) (v : I → K) :
    powerReplacement h₀ U selected v selected = v := by simp [powerReplacement]

/-- Every companion unary is kept exactly, up to the explicit field inclusion. -/
theorem powerReplacement_unchanged {ut : ℕ} (h₀ : K₀ ≤ K)
    (U : Fin ut → I → K₀) (selected : Fin ut) (v : I → K)
    (l : Fin ut) (hl : l.val ≠ selected.val) :
    powerReplacement h₀ U selected v l = fun i => IntermediateField.inclusion h₀ (U l i) := by
  exact Function.update_of_ne (fun h => hl (congrArg Fin.val h)) _ _

variable {q d e bt ut dt : ℕ}

/-- Actual fixed-slot replacement, including conversion back to the original
source oracle's field presentation after every interpolation query. -/
noncomputable def replacementReduction
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (selected : Fin ut) (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) :
    PromisePolyTimeTuringReduction
      (evaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (powerReplacement h₀ U selected v) (fun i => IntermediateField.inclusion h₀ (w i)))
      (evaluationProblem b₀ M U w) := by
  let φ := IntermediateField.inclusion h₀
  let liftedU := fun l i => φ (U l i)
  have hzero : ∀ i, liftedU selected i = 0 → powerReplacement h₀ U selected v selected i = 0 := by
    simpa only [powerReplacement_selected] using lifted_power_zero h₀ (U selected) v hpos
  have hproducts : HasProductMaps (liftedU selected) (powerReplacement h₀ U selected v selected) := by
    simpa only [powerReplacement_selected] using lifted_power_hasProductMaps h₀ (U selected) v hpos r hv
  exact (unaryProductReduction bK (fun l i j => φ (M l i j)) liftedU
    (powerReplacement h₀ U selected v) (fun i => φ (w i)) selected
    (powerReplacement_unchanged h₀ U selected v) hzero hproducts).trans
      (fieldMapReduction b₀ bK φ M U w)

/-- The same genuine algorithm on exactly the original prescribed domains and
endpoint/unary typing, without gaining unrestricted indicator or pinning power. -/
noncomputable def domainReplacementReduction
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (selected : Fin ut)
    (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (powerReplacement h₀ U selected v) (fun i => IntermediateField.inclusion h₀ (w i)) D B T)
      (domainEvaluationProblem b₀ M U w D B T) := by
  let φ := IntermediateField.inclusion h₀
  let liftedU := fun l i => φ (U l i)
  have hzero : ∀ i, liftedU selected i = 0 → powerReplacement h₀ U selected v selected i = 0 := by
    simpa only [powerReplacement_selected] using lifted_power_zero h₀ (U selected) v hpos
  have hproducts : HasProductMaps (liftedU selected) (powerReplacement h₀ U selected v selected) := by
    simpa only [powerReplacement_selected] using lifted_power_hasProductMaps h₀ (U selected) v hpos r hv
  exact (domainUnaryProductReduction bK (fun l i j => φ (M l i j)) liftedU
    (powerReplacement h₀ U selected v) (fun i => φ (w i)) D B T selected
    (powerReplacement_unchanged h₀ U selected v) hzero hproducts).trans
      (domainFieldMapReduction b₀ bK φ M U w D B T)

end PlanarHom.PositiveUnaryRationalPowers
