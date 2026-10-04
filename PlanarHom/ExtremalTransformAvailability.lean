import PlanarHom.SupportTransformAvailability
import PlanarHom.MagnitudeExtremaCompatibility

/-! Joint availability of all five source Corollary 3.2 transforms, with exact
attained magnitude extrema and all original constraints retained. -/
noncomputable section
namespace PlanarHom.SupportTransformAvailability
open Complexity Complexity.MixedCode ProductCompatibility AlgebraicProductInterpolation
variable {q bt ut : ℕ}

def fiveTransforms (M : Matrix (Fin q) (Fin q) ℝ) (a b : ℝ) :
    Fin 5 → Matrix (Fin q) (Fin q) ℝ :=
  ![fun i j => supportTransform (fun p : Fin q × Fin q => M p.1 p.2) (i,j),
    fun i j => |M i j|, fun i j => Real.sign (M i j),
    fun i j => extremalMask (fun p : Fin q × Fin q => |M p.1 p.2|) a (i,j),
    fun i j => extremalMask (fun p : Fin q × Fin q => |M p.1 p.2|) b (i,j)]

theorem fiveTransforms_algebraic (M : Matrix (Fin q) (Fin q) ℝ) (a b : ℝ)
    (hM : ∀ i j, IsAlgebraic ℚ (M i j)) : ∀ l i j, IsAlgebraic ℚ (fiveTransforms M a b l i j) := by
  intro l i j
  fin_cases l
  · exact supportTransform_isAlgebraic _ _
  · exact abs_isAlgebraic (hM i j)
  · exact sign_isAlgebraic _
  · exact extremalMask_isAlgebraic _ _ _
  · exact extremalMask_isAlgebraic _ _ _

theorem fiveTransforms_zero (M : Matrix (Fin q) (Fin q) ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b) :
    ∀ l i j, M i j = 0 → fiveTransforms M a b l i j = 0 := by
  intro l i j h
  fin_cases l
  · exact supportTransform_zero _ h
  · change |M i j| = 0
    rw [h, abs_zero]
  · change Real.sign (M i j) = 0
    rw [h, Real.sign_zero]
  · exact extremalMask_zero _ ha (by simpa only [h, abs_zero])
  · exact extremalMask_zero _ hb (by simpa only [h, abs_zero])

theorem fiveTransforms_products (M : Matrix (Fin q) (Fin q) ℝ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : ∀ i j, M i j ≠ 0 → a ≤ |M i j|) (hmax : ∀ i j, |M i j| ≤ b) :
    ∀ l, HasProductMaps (fun p : Fin q × Fin q => M p.1 p.2)
      (fun p => fiveTransforms M a b l p.1 p.2) := by
  intro l
  fin_cases l
  · exact hasProductMaps_support _
  · exact hasProductMaps_abs _
  · exact hasProductMaps_sign _
  · exact hasProductMaps_min_magnitude_mask _ a ha (fun p => hmin p.1 p.2)
  · exact hasProductMaps_max_magnitude_mask _ b hb (fun p => hmax p.1 p.2)

def fiveTransforms_joint (L : RealLanguage q bt ut) (old : Fin bt) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : ∀ i j, L.matrices old i j ≠ 0 → a ≤ |L.matrices old i j|)
    (hmax : ∀ i j, |L.matrices old i j| ≤ b)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction L.problem base) :=
  L.lemma31_mixedFinite (fiveTransforms (L.matrices old) a b) (fun i : Fin 0 => Fin.elim0 i)
    (fiveTransforms_algebraic _ a b (L.matrices_algebraic old)) (fun i => Fin.elim0 i)
    (fun _ => old) (fun i => Fin.elim0 i) (fiveTransforms_zero _ a b ha hb)
    (fiveTransforms_products _ a b ha hb hmin hmax) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) base available

def fiveTransforms_domain_joint {dt : ℕ} (L : RealLanguage q bt ut) (old : Fin bt)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hmin : ∀ i j, L.matrices old i j ≠ 0 → a ≤ |L.matrices old i j|)
    (hmax : ∀ i j, |L.matrices old i j| ≤ b)
    (D : Fin dt → Set (Fin q)) (B : Fin bt → Fin dt → Fin dt → Prop) (T : Fin ut → Fin dt → Prop)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction (L.domainProblem D B T) base) :=
  L.lemma31_domain_mixedFinite D B T (fiveTransforms (L.matrices old) a b) (fun i : Fin 0 => Fin.elim0 i)
    (fiveTransforms_algebraic _ a b (L.matrices_algebraic old)) (fun i => Fin.elim0 i)
    (fun _ => old) (fun i => Fin.elim0 i) (fiveTransforms_zero _ a b ha hb)
    (fiveTransforms_products _ a b ha hb hmin hmax) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) base available

/-- The extrema are the actual attained minimum nonzero magnitude and maximum
magnitude, rather than arbitrary threshold parameters supplied to the algorithm. -/
theorem exists_actual_extrema (M : Matrix (Fin q) (Fin q) ℝ) (hne : M ≠ 0) :
    ∃ a b : ℝ, 0 < a ∧ 0 < b ∧ (∃ i j, |M i j| = a) ∧ (∃ i j, |M i j| = b) ∧
      (∀ i j, M i j ≠ 0 → a ≤ |M i j|) ∧ (∀ i j, |M i j| ≤ b) := by
  have hnz : ∃ p : Fin q × Fin q, M p.1 p.2 ≠ 0 := by
    by_contra h
    apply hne
    funext i j
    exact not_ne_iff.mp (fun hne => h ⟨(i,j), hne⟩)
  obtain ⟨a,b,ha,hb,⟨ia,hia⟩,⟨ib,hib⟩,hmin,hmax⟩ :=
    exists_extremal_magnitudes (fun p : Fin q × Fin q => M p.1 p.2) hnz
  exact ⟨a,b,ha,hb,⟨ia.1,ia.2,hia⟩,⟨ib.1,ib.2,hib⟩,
    fun i j => hmin (i,j), fun i j => hmax (i,j)⟩

end PlanarHom.SupportTransformAvailability
