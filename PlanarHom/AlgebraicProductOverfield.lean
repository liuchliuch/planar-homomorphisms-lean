import PlanarHom.AlgebraicMixedLanguage
import PlanarHom.FiniteLanguageJointReductions
import PlanarHom.FieldPresentationReductions

/-! # Product interpolation over a fixed extension of the original output field

Only the fixed target constants are adjoined. The original source field and its
chosen basis remain the actual oracle presentation, through a compiled answer
conversion. Every old label coexists with the appended target label.
-/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation
open Complexity Complexity.MixedCode FixedAlgebraicField AlgebraicMixedLanguage
open FiniteLanguageAliases ProductCompatibility

variable {I : Type} [Fintype I]

/-- One fixed finite compositum; it never depends on an input graph. -/
def extensionField (K₀ : IntermediateField ℚ ℝ) (N : I → ℝ) : IntermediateField ℚ ℝ :=
  K₀ ⊔ commonField N

def sourceInclusion (K₀ : IntermediateField ℚ ℝ) (N : I → ℝ) :
    K₀ →ₐ[ℚ] extensionField K₀ N := IntermediateField.inclusion le_sup_left

def targetValue (K₀ : IntermediateField ℚ ℝ) (N : I → ℝ) (i : I) : extensionField K₀ N :=
  ⟨N i, (show commonField N ≤ extensionField K₀ N from le_sup_right) (mem_commonField N i)⟩

omit [Fintype I] in
@[simp] theorem sourceInclusion_coe (K₀ : IntermediateField ℚ ℝ) (N : I → ℝ) (x : K₀) :
    (sourceInclusion K₀ N x : ℝ) = x := rfl

omit [Fintype I] in
@[simp] theorem targetValue_coe (K₀ : IntermediateField ℚ ℝ) (N : I → ℝ) (i : I) :
    (targetValue K₀ N i : ℝ) = N i := rfl

theorem extension_finiteDimensional (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (N : I → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) :
    FiniteDimensional ℚ (extensionField K₀ N) := by
  letI := commonField_finiteDimensional N hN
  change FiniteDimensional ℚ ↥(K₀ ⊔ commonField N)
  infer_instance

def extensionBasis (K₀ : IntermediateField ℚ ℝ) [FiniteDimensional ℚ K₀]
    (N : I → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) :
    Module.Basis (Fin (Module.finrank ℚ (extensionField K₀ N))) ℚ (extensionField K₀ N) := by
  letI := extension_finiteDimensional K₀ N hN
  exact Module.finBasis ℚ _

variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]
variable {q dimension bt ut dt : ℕ}

/-- The actual binary Lemma 3.1 algorithm retains an arbitrary supplied source
field presentation while appending literal real-algebraic target entries. -/
def binaryOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j)) (old : Fin bt)
    (hzero : ∀ i j, (M old i j : ℝ) = 0 → N i j = 0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q => (M old p.1 p.2 : ℝ))
      (fun p => N p.1 p.2)) :
    let A := fun p : Fin q × Fin q => N p.1 p.2
    let φ := sourceInclusion K₀ A
    PromisePolyTimeTuringReduction
      (evaluationProblem (extensionBasis K₀ A (fun p => hN p.1 p.2))
        (appendOne (fun l i j => φ (M l i j)) (fun i j => targetValue K₀ A (i,j)))
        (fun l i => φ (U l i)) (fun i => φ (w i)))
      (evaluationProblem b₀ M U w) := by
  dsimp only
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion K₀ A
  let b := extensionBasis K₀ A (fun p => hN p.1 p.2)
  have hz : ∀ i j, φ (M old i j) = 0 → targetValue K₀ A (i,j) = 0 := by
    intro i j h
    apply Subtype.ext
    exact hzero i j (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hp : HasProductMaps (fun p : Fin q × Fin q => φ (M old p.1 p.2))
      (targetValue K₀ A) := hasProductMaps_lift _ _ _ hproducts
  exact (binaryAppendProductReduction b (fun l i j => φ (M l i j))
    (fun l i => φ (U l i)) (fun i => φ (w i)) (fun i j => targetValue K₀ A (i,j)) old hz hp).trans
      (fieldMapReduction b₀ b φ M U w)

/-- The same algorithm for unary functions, keeping their source label present. -/
def unaryOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) (old : Fin ut)
    (hzero : ∀ i, (U old i : ℝ) = 0 → N i = 0)
    (hproducts : HasProductMaps (fun i => (U old i : ℝ)) N) :
    let φ := sourceInclusion K₀ N
    PromisePolyTimeTuringReduction
      (evaluationProblem (extensionBasis K₀ N hN) (fun l i j => φ (M l i j))
        (appendOne (fun l i => φ (U l i)) (targetValue K₀ N)) (fun i => φ (w i)))
      (evaluationProblem b₀ M U w) := by
  dsimp only
  let φ := sourceInclusion K₀ N
  let b := extensionBasis K₀ N hN
  have hz : ∀ i, φ (U old i) = 0 → targetValue K₀ N i = 0 := by
    intro i h
    apply Subtype.ext
    exact hzero i (congrArg (fun x : extensionField K₀ N => (x : ℝ)) h)
  have hp : HasProductMaps (fun i => φ (U old i)) (targetValue K₀ N) :=
    hasProductMaps_lift _ _ _ hproducts
  exact (unaryAppendProductReduction b (fun l i j => φ (M l i j))
    (fun l i => φ (U l i)) (fun i => φ (w i)) (targetValue K₀ N) old hz hp).trans
      (fieldMapReduction b₀ b φ M U w)

/-- Prescribed vertex domains and allowed ordered endpoint types remain exact.
The appended target receives precisely the selected source label's type. -/
def domainBinaryOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (hN : ∀ i j, IsAlgebraic ℚ (N i j)) (old : Fin bt)
    (hzero : ∀ i j, (M old i j : ℝ) = 0 → N i j = 0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q => (M old p.1 p.2 : ℝ))
      (fun p => N p.1 p.2)) :
    let A := fun p : Fin q × Fin q => N p.1 p.2
    let φ := sourceInclusion K₀ A
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (extensionBasis K₀ A (fun p => hN p.1 p.2))
        (appendOne (fun l i j => φ (M l i j)) (fun i j => targetValue K₀ A (i,j)))
        (fun l i => φ (U l i)) (fun i => φ (w i)) D (appendOne B (B old)) T)
      (domainEvaluationProblem b₀ M U w D B T) := by
  dsimp only
  let A := fun p : Fin q × Fin q => N p.1 p.2
  let φ := sourceInclusion K₀ A
  let b := extensionBasis K₀ A (fun p => hN p.1 p.2)
  have hz : ∀ i j, φ (M old i j) = 0 → targetValue K₀ A (i,j) = 0 := by
    intro i j h
    apply Subtype.ext
    exact hzero i j (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hp : HasProductMaps (fun p : Fin q × Fin q => φ (M old p.1 p.2))
      (targetValue K₀ A) := hasProductMaps_lift _ _ _ hproducts
  exact (domainBinaryAppendProductReduction b (fun l i j => φ (M l i j))
    (fun l i => φ (U l i)) (fun i => φ (w i)) D B T
    (fun i j => targetValue K₀ A (i,j)) (B old) old (fun _ _ h => h) hz hp).trans
      (domainFieldMapReduction b₀ b φ M U w D B T)

/-- Unary domain aliases include the reserved-label offset correction. -/
def domainUnaryOverfieldReduction (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin q → ℝ) (hN : ∀ i, IsAlgebraic ℚ (N i)) (old : Fin ut)
    (hzero : ∀ i, (U old i : ℝ) = 0 → N i = 0)
    (hproducts : HasProductMaps (fun i => (U old i : ℝ)) N) :
    let φ := sourceInclusion K₀ N
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (extensionBasis K₀ N hN) (fun l i j => φ (M l i j))
        (appendOne (fun l i => φ (U l i)) (targetValue K₀ N)) (fun i => φ (w i))
        D B (appendOne T (T old)))
      (domainEvaluationProblem b₀ M U w D B T) := by
  dsimp only
  let φ := sourceInclusion K₀ N
  let b := extensionBasis K₀ N hN
  have hz : ∀ i, φ (U old i) = 0 → targetValue K₀ N i = 0 := by
    intro i h
    apply Subtype.ext
    exact hzero i (congrArg (fun x : extensionField K₀ N => (x : ℝ)) h)
  have hp : HasProductMaps (fun i => φ (U old i)) (targetValue K₀ N) :=
    hasProductMaps_lift _ _ _ hproducts
  exact (domainUnaryAppendProductReduction b (fun l i j => φ (M l i j))
    (fun l i => φ (U l i)) (fun i => φ (w i)) D B T (targetValue K₀ N) (T old) old
    (fun _ h => h) hz hp).trans (domainFieldMapReduction b₀ b φ M U w D B T)

end PlanarHom.AlgebraicProductInterpolation
