import PlanarHom.AlgebraicProductInterpolation

/-! # Simultaneous finite-family real-algebraic product interpolation

All appended binary and unary entries share one fixed finite overfield. Actual
finite-family interpolation is composed once with actual conversion from the
original source field and basis. There is no informal presentation-changing
induction and the number of input occurrences remains unrestricted.
-/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation
open Complexity Complexity.MixedCode FiniteLanguageAliases ProductCompatibility AlgebraicMixedLanguage
variable {q bt ut r s dt dimension : ℕ}

def finiteAlphabet (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ) :
    ((Fin r × Fin q × Fin q) ⊕ (Fin s × Fin q)) → ℝ :=
  Sum.elim (fun p => N p.1 p.2.1 p.2.2) (fun p => V p.1 p.2)

theorem finiteAlphabet_algebraic (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i)) :
    ∀ i, IsAlgebraic ℚ (finiteAlphabet N V i) := by
  intro i
  cases i with
  | inl p => exact hN p.1 p.2.1 p.2.2
  | inr p => exact hV p.1 p.2

def finiteBinaryValues (K₀ : IntermediateField ℚ ℝ)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (l : Fin r) (i j : Fin q) : extensionField K₀ (finiteAlphabet N V) :=
  targetValue K₀ (finiteAlphabet N V) (.inl (l,i,j))

def finiteUnaryValues (K₀ : IntermediateField ℚ ℝ)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (l : Fin s) (i : Fin q) : extensionField K₀ (finiteAlphabet N V) :=
  targetValue K₀ (finiteAlphabet N V) (.inr (l,i))

@[simp] theorem finiteBinaryValues_coe (K₀ : IntermediateField ℚ ℝ)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ) (l : Fin r) (i j : Fin q) :
    (finiteBinaryValues K₀ N V l i j : ℝ) = N l i j := rfl
@[simp] theorem finiteUnaryValues_coe (K₀ : IntermediateField ℚ ℝ)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ) (l : Fin s) (i : Fin q) :
    (finiteUnaryValues K₀ N V l i : ℝ) = V l i := rfl

variable {K₀ : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K₀]

/-- All finite targets coexist over one extension and reduce to the same supplied
source availability, in its original field basis. -/
def mixedFiniteOverfield_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i))
    (oldM : Fin r → Fin bt) (oldU : Fin s → Fin ut)
    (hzeroM : ∀ l i j, (M (oldM l) i j : ℝ) = 0 → N l i j = 0)
    (hproductsM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => (M (oldM l) p.1 p.2 : ℝ))
      (fun p => N l p.1 p.2))
    (hzeroU : ∀ l i, (U (oldU l) i : ℝ) = 0 → V l i = 0)
    (hproductsU : ∀ l, HasProductMaps (fun i => (U (oldU l) i : ℝ)) (V l))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (evaluationProblem b₀ M U w) base) :
    let A := finiteAlphabet N V
    let φ := sourceInclusion K₀ A
    PromisePolyTimeTuringReduction
      (evaluationProblem (extensionBasis K₀ A (finiteAlphabet_algebraic N V hN hV))
        (appendFamily (fun l i j => φ (M l i j)) (finiteBinaryValues K₀ N V))
        (appendFamily (fun l i => φ (U l i)) (finiteUnaryValues K₀ N V)) (fun i => φ (w i))) base := by
  dsimp only
  let A := finiteAlphabet N V
  let φ := sourceInclusion K₀ A
  let b := extensionBasis K₀ A (finiteAlphabet_algebraic N V hN hV)
  have hzM : ∀ l i j, φ (M (oldM l) i j) = 0 → finiteBinaryValues K₀ N V l i j = 0 := by
    intro l i j h
    apply Subtype.ext
    exact hzeroM l i j (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hzU : ∀ l i, φ (U (oldU l) i) = 0 → finiteUnaryValues K₀ N V l i = 0 := by
    intro l i h
    apply Subtype.ext
    exact hzeroU l i (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hpM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => φ (M (oldM l) p.1 p.2))
      (fun p => finiteBinaryValues K₀ N V l p.1 p.2) := fun l => hasProductMaps_lift _ _ _ (hproductsM l)
  have hpU : ∀ l, HasProductMaps (fun i => φ (U (oldU l) i)) (finiteUnaryValues K₀ N V l) :=
    fun l => hasProductMaps_lift _ _ _ (hproductsU l)
  exact mixedFiniteProduct_joint b (fun l i j => φ (M l i j)) (fun l i => φ (U l i))
    (fun i => φ (w i)) (finiteBinaryValues K₀ N V) (finiteUnaryValues K₀ N V)
    oldM oldU hzM hpM hzU hpU base ((fieldMapReduction b₀ b φ M U w).trans available)

/-- The same simultaneous finite-family algorithm preserves exact prescribed
domains and even permits a target's allowed types to be a subset of its source's. -/
def domainMixedFiniteOverfield_joint (b₀ : Module.Basis (Fin dimension) ℚ K₀)
    (M : Fin bt → Matrix (Fin q) (Fin q) K₀) (U : Fin ut → Fin q → K₀) (w : Fin q → K₀)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (BN : Fin r → Fin dt → Fin dt → Prop) (TV : Fin s → Fin dt → Prop)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i))
    (oldM : Fin r → Fin bt) (oldU : Fin s → Fin ut)
    (htypeM : ∀ l x y, BN l x y → B (oldM l) x y) (htypeU : ∀ l x, TV l x → T (oldU l) x)
    (hzeroM : ∀ l i j, (M (oldM l) i j : ℝ) = 0 → N l i j = 0)
    (hproductsM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => (M (oldM l) p.1 p.2 : ℝ))
      (fun p => N l p.1 p.2))
    (hzeroU : ∀ l i, (U (oldU l) i : ℝ) = 0 → V l i = 0)
    (hproductsU : ∀ l, HasProductMaps (fun i => (U (oldU l) i : ℝ)) (V l))
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem b₀ M U w D B T) base) :
    let A := finiteAlphabet N V
    let φ := sourceInclusion K₀ A
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem (extensionBasis K₀ A (finiteAlphabet_algebraic N V hN hV))
        (appendFamily (fun l i j => φ (M l i j)) (finiteBinaryValues K₀ N V))
        (appendFamily (fun l i => φ (U l i)) (finiteUnaryValues K₀ N V)) (fun i => φ (w i))
        D (appendFamily B BN) (appendFamily T TV)) base := by
  dsimp only
  let A := finiteAlphabet N V
  let φ := sourceInclusion K₀ A
  let b := extensionBasis K₀ A (finiteAlphabet_algebraic N V hN hV)
  have hzM : ∀ l i j, φ (M (oldM l) i j) = 0 → finiteBinaryValues K₀ N V l i j = 0 := by
    intro l i j h
    apply Subtype.ext
    exact hzeroM l i j (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hzU : ∀ l i, φ (U (oldU l) i) = 0 → finiteUnaryValues K₀ N V l i = 0 := by
    intro l i h
    apply Subtype.ext
    exact hzeroU l i (congrArg (fun x : extensionField K₀ A => (x : ℝ)) h)
  have hpM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => φ (M (oldM l) p.1 p.2))
      (fun p => finiteBinaryValues K₀ N V l p.1 p.2) := fun l => hasProductMaps_lift _ _ _ (hproductsM l)
  have hpU : ∀ l, HasProductMaps (fun i => φ (U (oldU l) i)) (finiteUnaryValues K₀ N V l) :=
    fun l => hasProductMaps_lift _ _ _ (hproductsU l)
  exact domainMixedFiniteProduct_joint b (fun l i j => φ (M l i j)) (fun l i => φ (U l i))
    (fun i => φ (w i)) D B T (finiteBinaryValues K₀ N V) (finiteUnaryValues K₀ N V) BN TV
    oldM oldU htypeM htypeU hzM hpM hzU hpU base
    ((domainFieldMapReduction b₀ b φ M U w D B T).trans available)

namespace RealLanguage
variable (L : RealLanguage q bt ut)

def mixedFiniteTargetProblem (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i)) : PromiseProblem :=
  let A := finiteAlphabet N V
  let φ := sourceInclusion L.field A
  evaluationProblem (extensionBasis L.field A (finiteAlphabet_algebraic N V hN hV))
    (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
    (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V)) (fun i => φ (L.weightsK i))

def domainMixedFiniteTargetProblem (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i))
    (oldM : Fin r → Fin bt) (oldU : Fin s → Fin ut) : PromiseProblem :=
  let A := finiteAlphabet N V
  let φ := sourceInclusion L.field A
  domainEvaluationProblem (extensionBasis L.field A (finiteAlphabet_algebraic N V hN hV))
    (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
    (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V)) (fun i => φ (L.weightsK i))
    D (appendFamily B (B ∘ oldM)) (appendFamily T (T ∘ oldU))

/-- The simultaneous extension-field answer is exactly the real partition sum
with both appended families present. -/
theorem mixedFiniteTarget_evaluate_coe
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (g : MixedCode) (hg : g.Valid (bt+r) (ut+s)) :
    let A := finiteAlphabet N V
    let φ := sourceInclusion L.field A
    (extensionField L.field A).val (g.evaluate hg
      (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
      (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V))
      (fun i => φ (L.weightsK i))) =
      g.evaluate hg (appendFamily L.matrices N) (appendFamily L.unaries V) L.weights := by
  dsimp only
  let A := finiteAlphabet N V
  let φ := sourceInclusion L.field A
  have hm : (fun l i j => ((appendFamily (fun l i j => φ (L.matricesK l i j))
      (finiteBinaryValues L.field N V) l i j) : ℝ)) = appendFamily L.matrices N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendFamily_old, appendFamily_old]; rfl
    · rw [appendFamily_new, appendFamily_new]; rfl
  have hu : (fun l i => ((appendFamily (fun l i => φ (L.unariesK l i))
      (finiteUnaryValues L.field N V) l i) : ℝ)) = appendFamily L.unaries V := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendFamily_old, appendFamily_old]; rfl
    · rw [appendFamily_new, appendFamily_new]; rfl
  have h := map_evaluate (extensionField L.field A).val.toRingHom g hg
      (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
      (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V))
      (fun i => φ (L.weightsK i))
  change _ = g.evaluate hg (fun l i j => ((appendFamily (fun l i j => φ (L.matricesK l i j))
      (finiteBinaryValues L.field N V) l i j) : ℝ))
      (fun l i => ((appendFamily (fun l i => φ (L.unariesK l i))
      (finiteUnaryValues L.field N V) l i) : ℝ)) L.weights at h
  rw [hm, hu] at h
  exact h

/-- The same exact real identity with every prescribed vertex domain unchanged. -/
theorem mixedFiniteTarget_evaluateRestricted_coe
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (g : MixedCode) (hg : g.Valid (bt+r) (ut+s))
    (D : Fin dt → Set (Fin q)) (δ : Fin g.vertices → Fin dt) :
    let A := finiteAlphabet N V
    let φ := sourceInclusion L.field A
    (extensionField L.field A).val (PrescribedDomains.evaluateRestricted g hg
      (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
      (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V))
      (fun i => φ (L.weightsK i)) D δ) =
      PrescribedDomains.evaluateRestricted g hg (appendFamily L.matrices N) (appendFamily L.unaries V) L.weights D δ := by
  dsimp only
  let A := finiteAlphabet N V
  let φ := sourceInclusion L.field A
  have hm : (fun l i j => ((appendFamily (fun l i j => φ (L.matricesK l i j))
      (finiteBinaryValues L.field N V) l i j) : ℝ)) = appendFamily L.matrices N := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendFamily_old, appendFamily_old]; rfl
    · rw [appendFamily_new, appendFamily_new]; rfl
  have hu : (fun l i => ((appendFamily (fun l i => φ (L.unariesK l i))
      (finiteUnaryValues L.field N V) l i) : ℝ)) = appendFamily L.unaries V := by
    funext l
    refine Fin.addCases (fun k => ?_) (fun k => ?_) l
    · rw [appendFamily_old, appendFamily_old]; rfl
    · rw [appendFamily_new, appendFamily_new]; rfl
  have h := PrescribedDomains.map_evaluateRestricted (extensionField L.field A).val.toRingHom g hg
      (appendFamily (fun l i j => φ (L.matricesK l i j)) (finiteBinaryValues L.field N V))
      (appendFamily (fun l i => φ (L.unariesK l i)) (finiteUnaryValues L.field N V))
      (fun i => φ (L.weightsK i)) D δ
  change _ = PrescribedDomains.evaluateRestricted g hg (fun l i j => ((appendFamily (fun l i j => φ (L.matricesK l i j))
      (finiteBinaryValues L.field N V) l i j) : ℝ))
      (fun l i => ((appendFamily (fun l i => φ (L.unariesK l i))
      (finiteUnaryValues L.field N V) l i) : ℝ)) L.weights D δ at h
  rw [hm, hu] at h
  exact h

/-- Any fixed finite binary/unary target family is jointly available in one
common field, all at once, from the original supplied source availability. -/
def lemma31_mixedFinite (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i))
    (oldM : Fin r → Fin bt) (oldU : Fin s → Fin ut)
    (hzeroM : ∀ l i j, L.matrices (oldM l) i j = 0 → N l i j = 0)
    (hproductsM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => L.matrices (oldM l) p.1 p.2)
      (fun p => N l p.1 p.2))
    (hzeroU : ∀ l i, L.unaries (oldU l) i = 0 → V l i = 0)
    (hproductsU : ∀ l, HasProductMaps (L.unaries (oldU l)) (V l))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :
    PromisePolyTimeTuringReduction (L.mixedFiniteTargetProblem N V hN hV) base :=
  mixedFiniteOverfield_joint L.basis L.matricesK L.unariesK L.weightsK N V hN hV oldM oldU
    hzeroM hproductsM hzeroU hproductsU base available

/-- The finite-family statement with all prescribed domains retained. -/
def lemma31_domain_mixedFinite (D : Fin dt → Set (Fin q))
    (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (N : Fin r → Matrix (Fin q) (Fin q) ℝ) (V : Fin s → Fin q → ℝ)
    (hN : ∀ l i j, IsAlgebraic ℚ (N l i j)) (hV : ∀ l i, IsAlgebraic ℚ (V l i))
    (oldM : Fin r → Fin bt) (oldU : Fin s → Fin ut)
    (hzeroM : ∀ l i j, L.matrices (oldM l) i j = 0 → N l i j = 0)
    (hproductsM : ∀ l, HasProductMaps (fun p : Fin q × Fin q => L.matrices (oldM l) p.1 p.2)
      (fun p => N l p.1 p.2))
    (hzeroU : ∀ l i, L.unaries (oldU l) i = 0 → V l i = 0)
    (hproductsU : ∀ l, HasProductMaps (L.unaries (oldU l)) (V l))
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :
    PromisePolyTimeTuringReduction (L.domainMixedFiniteTargetProblem D B T N V hN hV oldM oldU) base :=
  domainMixedFiniteOverfield_joint L.basis L.matricesK L.unariesK L.weightsK D B T N V
    (B ∘ oldM) (T ∘ oldU) hN hV oldM oldU (fun _ _ _ h => h) (fun _ _ h => h)
    hzeroM hproductsM hzeroU hproductsU base available

end RealLanguage
end PlanarHom.AlgebraicProductInterpolation
