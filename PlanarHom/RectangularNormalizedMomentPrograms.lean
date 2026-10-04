import PlanarHom.VertexMomentUnarySource
import PlanarHom.RectangularSquareNormSource

/-!
# Normalized rectangular fixed-moment source programs — NEW reconstruction

Compose the newly compiled endpoint/all-vertex unary programs with the actual
constructed inverse-norm unary. The source oracle is the original weighted
block, with its original field and output basis. No availability assumption is
accepted. Actual numerical twin quotienting is then the baseline identity-query
program. This does not supply independent left/right prescribed-domain powers.
-/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.EndpointUnarySource
open Complexity Complexity.MixedCode FiniteLanguageAliases
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension b u : ℕ}

/-- Compile both endpoint gauge and fixed all-vertex moment factors. -/
def gaugeMomentReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K)
    (old : Fin b) (gauge moment : Fin u) (power : ℕ) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (appendOne M (unaryGauge (M old) (U gauge))) U
        (fun i => w i * (U moment i)^power))
      (evaluationProblem basis M U w) :=
  gaugeMomentOneQueryReduction basis M U w old gauge moment power

/-- Restriction to a selected binary and no explicit unaries is implemented by
real finite-label machines; no language inclusion is treated as free. -/
def selectedMatrixReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix C C K) (U : Fin u → C → K) (w : C → K) (selected : Fin b) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _ : Fin 1 => M selected) (fun l : Fin 0 => l.elim0) w)
      (evaluationProblem basis M U w) := by
  have binary := binaryRelabelReduction basis (fun _ : Fin 1 => selected) M U w
  have unary := unaryRelabelReduction basis (fun l : Fin 0 => l.elim0)
    (fun _ : Fin 1 => M selected) U w
  have hu : U ∘ (fun l : Fin 0 => l.elim0) = (fun l : Fin 0 => l.elim0) := by
    funext l
    exact l.elim0
  simpa only [hu] using unary.trans binary

end PlanarHom.EndpointUnarySource

namespace PlanarHom.RectangularBackgroundSourceNormSimulation
open Complexity Complexity.MixedCode FiniteLanguageAliases EndpointUnarySource
open RectangularSourceNormSimulation RectangularWeightedNormNormalization
variable {p s d n : ℕ} {K₀ F : IntermediateField ℚ ℝ}
variable [Nonempty (Fin p)] [Nonempty (Fin s)]

omit [Nonempty (Fin p)] [Nonempty (Fin s)] in
/-- The endpoint gauge is exactly the paper's weighted normalized block. -/
theorem inverse_norm_gauge_real (h₀ : K₀ ≤ F)
    (V : Matrix (Fin p) (Fin s) K₀) (μ : Fin p → K₀) (ν : Fin s → K₀)
    (v : Fin (p+s) → F)
    (hv : ∀ i, (v i : ℝ) =
      (norm (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ)) i)⁻¹) :
    (fun i j => (unaryGauge (fun i j => IntermediateField.inclusion h₀ (block V i j)) v i j : ℝ)) =
      block (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) := by
  funext i j
  change (v i : ℝ) * (block V i j : ℝ) * (v j : ℝ) = _
  rw [hv i,hv j]
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;>
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      simp only [block_left_left, block_left_right, block_right_left, block_right_right,
        norm, Fin.addCases_left, Fin.addCases_right, normalized, realRectangular]
  · simp
  · simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · simp only [div_eq_mul_inv,mul_inv_rev]
    ring
  · simp

/-- One field and normalized matrix work for every fixed natural moment.
Every reduction is built from real raw-codec programs and returns to the exact
original source basis. -/
theorem exists_rectangular_normalized_moment_sources
    (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j, 0 < (V i j : ℝ))
    (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ)) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (C : Matrix (Fin (p+s)) (Fin (p+s)) F),
      (∀ i j, C i j = C j i) ∧
      (fun i j => (C i j : ℝ)) =
        block (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) ∧
      (∀ m : ℕ, Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun _ : Fin 1 => C) (fun l : Fin 0 => l.elim0)
          (fun i => IntermediateField.inclusion h₀ (weights μ ν i) *
            (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m))
        (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν)))) := by
  obtain ⟨F,h₀,e,bF,v,hv,⟨source⟩⟩ := exists_rectangular_inverse_norm_unary basis V hV μ ν hμ hν
  let M : Fin 1 → Matrix (Fin (p+s)) (Fin (p+s)) F :=
    fun _ i j => IntermediateField.inclusion h₀ (block V i j)
  let U : Fin 2 → Fin (p+s) → F := appendOne
    (fun l i => IntermediateField.inclusion h₀
      (appendOne (fun l : Fin 0 => l.elim0) (squareNorm (block V) (weights μ ν)) l i)) v
  let w : Fin (p+s) → F := fun i => IntermediateField.inclusion h₀ (weights μ ν i)
  let C := unaryGauge (M 0) v
  have hU0 : U 0 = fun i => IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i) := by
    funext i
    change appendOne _ v (Fin.castAdd 1 (0 : Fin 1)) i = _
    rw [appendOne_old]
    change IntermediateField.inclusion h₀ (appendOne (fun l : Fin 0 => l.elim0)
      (squareNorm (block V) (weights μ ν)) (Fin.last 0) i) = _
    rw [appendOne_aux]
  have hU1 : U 1 = v := by
    change appendOne _ v (Fin.last 1) = _
    rw [appendOne_aux]
  have hC : (fun i j => (C i j : ℝ)) =
      block (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) :=
    inverse_norm_gauge_real h₀ V μ ν v hv
  have hs : ∀ i j, C i j = C j i := by
    intro i j
    apply Subtype.ext
    rw [show (C i j : ℝ) = block (normalized (realRectangular V)
      (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) i j from congrFun (congrFun hC i) j]
    rw [show (C j i : ℝ) = block (normalized (realRectangular V)
      (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) j i from congrFun (congrFun hC j) i]
    exact block_symm _ i j
  refine ⟨F,h₀,e,bF,C,hs,hC,?_⟩
  intro m
  have stage := (gaugeMomentReduction bF M U w 0 1 0 m).trans source
  rw [hU1,hU0] at stage
  have selected := selectedMatrixReduction bF (appendOne M C) U
    (fun i => w i * (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^m) (Fin.last 1)
  simp only [appendOne_aux] at selected
  exact ⟨selected.trans stage⟩

/-- The exact finite-family existence API consumed by the surviving
RectangularSideMomentPresentation. The source program is constructed above;
quotienting is the certified same-raw-graph reduction. -/
theorem exists_rectangular_quotient_moment_sources
    (basis : Module.Basis (Fin d) ℚ K₀)
    (V : Matrix (Fin p) (Fin s) K₀) (hV : ∀ i j, 0 < (V i j : ℝ))
    (μ : Fin p → K₀) (ν : Fin s → K₀)
    (hμ : ∀ i, 0 < (μ i : ℝ)) (hν : ∀ j, 0 < (ν j : ℝ)) (ms : Fin n → ℕ) :
    ∃ (F : IntermediateField ℚ ℝ) (h₀ : K₀ ≤ F) (e : ℕ)
      (bF : Module.Basis (Fin e) ℚ F) (C : Matrix (Fin (p+s)) (Fin (p+s)) F)
      (hs : ∀ i j, C i j = C j i),
      (fun i j => (C i j : ℝ)) =
        block (normalized (realRectangular V) (fun i => (μ i : ℝ)) (fun j => (ν j : ℝ))) ∧
      (∀ l : Fin n, Nonempty (PromisePolyTimeTuringReduction
        (evaluationProblem bF (fun _ : Fin 1 => Twins.quotientMatrix C hs) (fun l : Fin 0 => l.elim0)
          (Twins.quotientWeight C (fun i => IntermediateField.inclusion h₀ (weights μ ν i) *
            (IntermediateField.inclusion h₀ (squareNorm (block V) (weights μ ν) i))^(ms l))))
        (evaluationProblem basis (fun _ : Fin 1 => block V) (fun l : Fin 0 => l.elim0) (weights μ ν)))) := by
  obtain ⟨F,h₀,e,bF,C,hs,hC,hr⟩ := exists_rectangular_normalized_moment_sources basis V hV μ ν hμ hν
  refine ⟨F,h₀,e,bF,C,hs,hC,?_⟩
  intro l
  obtain ⟨r⟩ := hr (ms l)
  exact ⟨(ActualTwins.quotientReduction bF C hs _).trans r⟩

end PlanarHom.RectangularBackgroundSourceNormSimulation
