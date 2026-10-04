import PlanarHom.PositiveUnaryPowerReductions
import PlanarHom.PrescribedDomainAliasReductions

/-!
# Genuine joint availability of a positive unary's fixed rational power

The new unary gets an appended label; every original unary and binary label is
retained. Actual interpolation, fixed-field answer conversion and finite-label
alias machines are composed, with the original source oracle presentation and
prescribed domains unchanged. The finite extension and actual powered values
are constructed from the fixed data, for negative and zero exponents as well.
-/

noncomputable section
open Classical
namespace PlanarHom.PositiveUnaryRationalPowers
open ProductCompatibility Complexity Complexity.MixedCode FiniteLanguageAliases
variable {I : Type} {K₀ K : IntermediateField ℚ ℝ}

/-- Replacing the appended duplicate gives exactly the appended target language. -/
theorem powerReplacement_appendOne {ut : ℕ} (h₀ : K₀ ≤ K)
    (U : Fin ut → I → K₀) (selected : Fin ut) (v : I → K) :
    powerReplacement h₀ (appendOne U (U selected)) (Fin.last ut) v =
      appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v := by
  funext l
  refine Fin.addCases ?_ ?_ l
  · intro i
    have hne : (Fin.castAdd 1 i).val ≠ (Fin.last ut).val := by
      simp only [Fin.coe_castAdd, Fin.val_last]
      exact Nat.ne_of_lt i.isLt
    rw [powerReplacement_unchanged _ _ _ _ _ hne, appendOne_old, appendOne_old]
  · intro i
    have hi : i = (0 : Fin 1) := Subsingleton.elim _ _
    subst i
    change powerReplacement h₀ (appendOne U (U selected)) (Fin.last ut) v (Fin.last ut) = _
    rw [powerReplacement_selected]
    simp [appendOne]

variable {q d e bt ut dt : ℕ}

/-- Actual ordinary-planar joint extension by one powered unary, retaining all
old labels and the old source output basis. -/
noncomputable def appendedPowerReduction
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (selected : Fin ut) (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) :
    PromisePolyTimeTuringReduction
      (evaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
        (fun i => IntermediateField.inclusion h₀ (w i)))
      (evaluationProblem b₀ M U w) := by
  have stage := replacementReduction b₀ bK h₀ M (appendOne U (U selected)) w (Fin.last ut)
    (by simpa only [appendOne_aux] using hpos) r v (by simpa only [appendOne_aux] using hv)
  have aliasReduction : PromisePolyTimeTuringReduction
      (evaluationProblem b₀ M (appendOne U (U selected)) w) (evaluationProblem b₀ M U w) := by
    simpa only [comp_aliasAux] using unaryRelabelReduction b₀ (aliasAux selected) M U w
  simpa only [powerReplacement_appendOne] using stage.trans aliasReduction

/-- Appending a powered unary uses the same allowed domain types as its source,
retains every original type, and moves reserved domain metadata by the proved
alias compiler rather than assuming the two raw encodings coincide. -/
noncomputable def domainAppendedPowerReduction
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (selected : Fin ut)
    (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
        (fun i => IntermediateField.inclusion h₀ (w i)) D B (appendOne T (T selected)))
      (domainEvaluationProblem b₀ M U w D B T) := by
  have stage := domainReplacementReduction b₀ bK h₀ M (appendOne U (U selected)) w D B
    (appendOne T (T selected)) (Fin.last ut) (by simpa only [appendOne_aux] using hpos)
    r v (by simpa only [appendOne_aux] using hv)
  simpa only [powerReplacement_appendOne] using stage.trans
    (domainUnaryDuplicateReduction b₀ M U w D B T selected)

/-- The original supplied joint simulation composes with the actual appended
power construction, keeping all original companion constraints present. -/
noncomputable def appendedPower_joint
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (selected : Fin ut) (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem b₀ M U w) base) :
    PromisePolyTimeTuringReduction
      (evaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
        (fun i => IntermediateField.inclusion h₀ (w i))) base :=
  (appendedPowerReduction b₀ bK h₀ M U w selected hpos r v hv).trans available

/-- Joint availability with all original domain restrictions and the original
source oracle's output representation. -/
noncomputable def domainAppendedPower_joint
    (b₀ : Module.Basis (Fin d) ℚ K₀) (bK : Module.Basis (Fin e) ℚ K) (h₀ : K₀ ≤ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (selected : Fin ut)
    (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (v : Fin q → K) (hv : ∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ))
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem b₀ M U w D B T) base) :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
        (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
        (fun i => IntermediateField.inclusion h₀ (w i)) D B (appendOne T (T selected))) base :=
  (domainAppendedPowerReduction b₀ bK h₀ M U w D B T selected hpos r v hv).trans available

/-- The ordinary positive-unary rational-power corollary with the finite target
field, its basis, its actual power values and its real algorithm all constructed. -/
theorem exists_joint_power_available
    (b₀ : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (selected : Fin ut) (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem b₀ M U w) base) :
    ∃ (K : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ K) (e : ℕ) (bK : Module.Basis (Fin e) ℚ K)
      (v : Fin q → K),
      (∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
          (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
          (fun i => IntermediateField.inclusion h₀ (w i))) base) := by
  letI := FiniteDimensional.of_fintype_basis b₀
  obtain ⟨K, h₀, hK, v, hv, _, _, _⟩ := exists_fixed_power_overfield K₀ (U selected) hpos r
  letI : FiniteDimensional ℚ K := hK
  let bK := Module.finBasis ℚ K
  exact ⟨K, h₀, Module.finrank ℚ K, bK, v, hv,
    ⟨appendedPower_joint b₀ bK h₀ M U w selected hpos r v hv base available⟩⟩

/-- The same complete construction retains every original prescribed domain,
with the new label allowed exactly wherever the original selected unary was. -/
theorem exists_domain_joint_power_available
    (b₀ : Module.Basis (Fin d) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop)
    (T : Fin ut → Fin dt → Prop) (selected : Fin ut)
    (hpos : ∀ i, 0 < (U selected i : ℝ)) (r : ℚ)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem b₀ M U w D B T) base) :
    ∃ (K : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ K) (e : ℕ) (bK : Module.Basis (Fin e) ℚ K)
      (v : Fin q → K),
      (∀ i, (v i : ℝ) = (U selected i : ℝ) ^ (r : ℝ)) ∧
      Nonempty (PromisePolyTimeTuringReduction
        (domainEvaluationProblem bK (fun l i j => IntermediateField.inclusion h₀ (M l i j))
          (appendOne (fun l i => IntermediateField.inclusion h₀ (U l i)) v)
          (fun i => IntermediateField.inclusion h₀ (w i)) D B (appendOne T (T selected))) base) := by
  letI := FiniteDimensional.of_fintype_basis b₀
  obtain ⟨K, h₀, hK, v, hv, _, _, _⟩ := exists_fixed_power_overfield K₀ (U selected) hpos r
  letI : FiniteDimensional ℚ K := hK
  let bK := Module.finBasis ℚ K
  exact ⟨K, h₀, Module.finrank ℚ K, bK, v, hv,
    ⟨domainAppendedPower_joint b₀ bK h₀ M U w D B T selected hpos r v hv base available⟩⟩

end PlanarHom.PositiveUnaryRationalPowers
