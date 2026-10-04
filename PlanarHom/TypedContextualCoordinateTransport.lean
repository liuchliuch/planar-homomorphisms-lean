import PlanarHom.PrescribedDomainColorTransport
import PlanarHom.TypedContextualMatrixAvailability

/-! NEW RECONSTRUCTION (2026-10-02). Coordinate transport in the actual canonical
real-language API. Arbitrary retained labels are universally quantified. Every
bridge realizes coefficients in the destination language's original field and
uses the existing field-presentation compiler; no field-code equality is assumed.
-/
noncomputable section
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {q q' bt ut dt dt' s : ℕ}

/-- Pull back every original coefficient; no labels are dropped or adjoined. -/
def coordinatePullback (L : RealLanguage q bt ut) (e : Fin q' ≃ Fin q) :
    RealLanguage q' bt ut where
  matrices := fun l i j => L.matrices l (e i) (e j)
  unaries := fun l i => L.unaries l (e i)
  weights := fun i => L.weights (e i)
  matrices_algebraic := fun l i j => L.matrices_algebraic l (e i) (e j)
  unaries_algebraic := fun l i => L.unaries_algebraic l (e i)
  weights_algebraic := fun i => L.weights_algebraic (e i)

/-- Ordinary source bridge for the side swap. In particular, non-hardness need
only be assumed for the original source, never for an unrelated swapped oracle. -/
def coordinateReduction (target : RealLanguage q' bt ut) (source : RealLanguage q bt ut)
    (e : Fin q' ≃ Fin q)
    (hM : ∀ l i j, target.matrices l i j = source.matrices l (e i) (e j))
    (hU : ∀ l i, target.unaries l i = source.unaries l (e i))
    (hw : ∀ i, target.weights i = source.weights (e i)) :
    PromisePolyTimeTuringReduction target.problem source.problem := by
  have present := target.presentationDescentReduction source.field source.basis
    (fun l i j => source.matricesK l (e i) (e j))
    (fun l i => source.unariesK l (e i)) (fun i => source.weightsK (e i))
    (fun l i j => (hM l i j).symm) (fun l i => (hU l i).symm) (fun i => (hw i).symm)
  exact present.transport _ _ (fun _ h => h) (fun _ h => h) (fun _ _ => rfl)
    (fun raw _ => (congrFun (evaluationValue_reindexColors source.basis e
      source.matricesK source.unariesK source.weightsK) raw).symm)

/-- Fully represented transport to the source's original coefficient field. The
only changed graph labels are the reserved intrinsic-domain labels. -/
def typedCoordinateReduction (target : RealLanguage q' bt ut) (source : RealLanguage q bt ut)
    (e : Fin q' ≃ Fin q) (ρ : Fin dt' → Fin dt)
    (D : Fin dt → Set (Fin q)) (D' : Fin dt' → Set (Fin q'))
    (BT : Fin bt → Fin dt' → Fin dt' → Prop) (BS : Fin bt → Fin dt → Fin dt → Prop)
    (TT : Fin ut → Fin dt' → Prop) (TS : Fin ut → Fin dt → Prop)
    (hD : ∀ d, D' d = e ⁻¹' D (ρ d))
    (hB : ∀ l x y, BT l x y → BS l (ρ x) (ρ y))
    (hT : ∀ l x, TT l x → TS l (ρ x))
    (hM : ∀ l i j, target.matrices l i j = source.matrices l (e i) (e j))
    (hU : ∀ l i, target.unaries l i = source.unaries l (e i))
    (hw : ∀ i, target.weights i = source.weights (e i)) :
    PromisePolyTimeTuringReduction (target.typedProblem D' BT TT) (source.typedProblem D BS TS) := by
  have hd : D' = fun d => e ⁻¹' D (ρ d) := funext hD
  subst D'
  let M := fun l i j => source.matricesK l (e i) (e j)
  let U := fun l i => source.unariesK l (e i)
  let w := fun i => source.weightsK (e i)
  have present := target.typedPresentationDescentReduction (fun d => e ⁻¹' D (ρ d)) BT TT source.field source.basis M U w
    (fun l i j => (hM l i j).symm) (fun l i => (hU l i).symm) (fun i => (hw i).symm)
  have color := domainColorReindexReduction source.basis e source.matricesK source.unariesK
    source.weightsK (D ∘ ρ) BT TT
  have domain := domainReindexReduction source.basis ρ source.matricesK source.unariesK
    source.weightsK D BT BS TT TS hB hT
  exact present.trans (color.trans domain)

/-- Actual contextual availability survives simultaneous color and domain
bijections. The context still ranges over every retained matrix and unary label,
with the exact transported endpoint policies and unit background. -/
theorem typed_contextual_coordinate_pullback
    (e : Fin q' ≃ Fin q) (ρ : Fin dt' ≃ Fin dt)
    (D : Fin dt → Set (Fin q)) (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (FB : Fin s → Fin dt → Fin dt → Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (NB : Fin dt → Fin dt → Prop)
    (hN : TypedContextuallyAvailable D F FB N NB) :
    TypedContextuallyAvailable (fun d => e ⁻¹' D (ρ d))
      (fun l i j => F l (e i) (e j)) (fun l a b => FB l (ρ a) (ρ b))
      (fun i j => N (e i) (e j)) (fun a b => NB (ρ a) (ρ b)) := by
  refine ⟨fun i j => hN.algebraic (e i) (e j), ?_⟩
  intro bt ut L B T hunit hF
  let V := L.coordinatePullback e.symm
  let BV := fun l a b => B l (ρ.symm a) (ρ.symm b)
  let TV := fun l a => T l (ρ.symm a)
  have hVunit : ∀ i, V.weights i = 1 := fun i => hunit (e.symm i)
  have hVF : V.ContainsTypedMatrices BV F FB := by
    obtain ⟨index, hi⟩ := hF
    refine ⟨index, fun l => ⟨?_, ?_⟩⟩
    · funext i j
      have h := congrFun (congrFun (hi l).1 (e.symm i)) (e.symm j)
      simpa only [V, coordinatePullback, Equiv.apply_symm_apply] using h
    · funext a b
      have h := congrFun (congrFun (hi l).2 (ρ.symm a)) (ρ.symm b)
      simpa only [BV, Equiv.apply_symm_apply] using h
  obtain ⟨middle⟩ := hN.reduction V BV TV hVunit hVF
  have before := typedCoordinateReduction
    (L.appendBinary (fun i j => N (e i) (e j)) (fun i j => hN.algebraic (e i) (e j)))
    (V.appendBinary N hN.algebraic) e ρ D (fun d => e ⁻¹' D (ρ d))
    (appendOne B (fun a b => NB (ρ a) (ρ b))) (appendOne BV NB) T TV
    (fun _ => rfl)
    (by
      intro l
      refine Fin.addCases (fun k => ?_) (fun k => ?_) l
      · intro a b h
        simpa only [appendOne_old, BV, Equiv.symm_apply_apply] using h
      · intro a b h
        simpa only [appendOne, Fin.addCases_right] using h)
    (by intro l a h; simpa only [TV, Equiv.symm_apply_apply] using h)
    (by
      intro l
      refine Fin.addCases (fun k => ?_) (fun k => ?_) l
      · intro i j
        simp only [appendBinary, appendOne_old, V, coordinatePullback, Equiv.symm_apply_apply]
      · intro i j
        simp only [appendBinary, appendOne, Fin.addCases_right])
    (by intro l i; simp only [appendBinary, V, coordinatePullback, Equiv.symm_apply_apply])
    (by intro i; simp only [appendBinary, V, coordinatePullback, Equiv.symm_apply_apply])
  have after := typedCoordinateReduction V L e.symm ρ.symm
    (fun d => e ⁻¹' D (ρ d)) D BV B TV T
    (by
      intro d
      apply Set.ext
      intro i
      simp only [Set.mem_preimage, Equiv.apply_symm_apply])
    (fun _ _ _ h => h) (fun _ _ h => h)
    (fun _ _ _ => rfl) (fun _ _ => rfl) (fun _ => rfl)
  exact ⟨before.trans (middle.trans after)⟩

/-- Both directions use the same actual arbitrary-context transport. -/
theorem typed_contextual_coordinate_pullback_iff
    (e : Fin q' ≃ Fin q) (ρ : Fin dt' ≃ Fin dt)
    (D : Fin dt → Set (Fin q)) (F : Fin s → Matrix (Fin q) (Fin q) ℝ)
    (FB : Fin s → Fin dt → Fin dt → Prop)
    (N : Matrix (Fin q) (Fin q) ℝ) (NB : Fin dt → Fin dt → Prop) :
    TypedContextuallyAvailable (fun d => e ⁻¹' D (ρ d))
      (fun l i j => F l (e i) (e j)) (fun l a b => FB l (ρ a) (ρ b))
      (fun i j => N (e i) (e j)) (fun a b => NB (ρ a) (ρ b)) ↔
    TypedContextuallyAvailable D F FB N NB := by
  constructor
  · intro h
    have inverse := typed_contextual_coordinate_pullback e.symm ρ.symm
      (fun d => e ⁻¹' D (ρ d))
      (fun l i j => F l (e i) (e j)) (fun l a b => FB l (ρ a) (ρ b))
      (fun i j => N (e i) (e j)) (fun a b => NB (ρ a) (ρ b)) h
    have hd : (fun d => e.symm ⁻¹' (e ⁻¹' D d)) = D := by
      funext d
      apply Set.ext
      intro i
      simp only [Set.mem_preimage, Equiv.apply_symm_apply]
    simpa only [Equiv.apply_symm_apply, hd] using inverse
  · exact typed_contextual_coordinate_pullback e ρ D F FB N NB

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
