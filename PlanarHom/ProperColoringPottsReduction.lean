import PlanarHom.PromisedSharpPHardness
import PlanarHom.ProductInterpolationReductions
import PlanarHom.RootedHomogeneousSemantics

/-!
# NEW reconstruction: actual planar proper-coloring to positive Potts reduction

The source is the literal proper q-coloring partition function. The target is
I_q+J_q, with diagonal 2 and off-diagonal 1. The existing product-interpolation
compiler physically produces parallel-edge queries and evaluates the recovery
program in polynomial bit time. All source promises and answer costs are paid.

This proves a concrete reduction gate. It does not assert #P-hardness of planar
three-coloring, which is a separate absent foundational theorem.
-/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.ProperColoringPottsReduction
open Complexity Complexity.MixedCode ProductCompatibility

/-- The literal proper-coloring edge indicator. -/
def coloringMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := fun i j => if i=j then 0 else 1

/-- The literal positive Potts matrix I+J. -/
def positivePottsMatrix (q : ℕ) : Matrix (Fin q) (Fin q) ℚ := fun i j => if i=j then 2 else 1

/-- The displayed positive source really is the paper's I+J matrix. -/
theorem positivePottsMatrix_eq (q : ℕ) :
    positivePottsMatrix q = (1 : Matrix (Fin q) (Fin q) ℚ) + Matrix.of (fun _ _ => 1) := by
  ext i j
  by_cases h : i=j <;> norm_num [positivePottsMatrix, Matrix.one_apply, h]

/-- Number of diagonal factors in an actual source alphabet word. -/
def diagonalCount {q : ℕ} (xs : List (Fin q × Fin q)) : ℕ :=
  xs.countP (fun p => decide (p.1=p.2))

theorem potts_product {q : ℕ} (xs : List (Fin q × Fin q)) :
    (xs.map (fun p => positivePottsMatrix q p.1 p.2)).prod = (2:ℚ)^diagonalCount xs := by
  induction xs with
  | nil => simp [diagonalCount]
  | cons p xs ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases hp : p.1=p.2 <;>
      simp [positivePottsMatrix, diagonalCount, hp, pow_succ, mul_comm]

theorem coloring_product {q : ℕ} (xs : List (Fin q × Fin q)) :
    (xs.map (fun p => coloringMatrix q p.1 p.2)).prod =
      if diagonalCount xs=0 then 1 else 0 := by
  induction xs with
  | nil => simp [diagonalCount]
  | cons p xs ih =>
    rw [List.map_cons, List.prod_cons, ih]
    by_cases hp : p.1=p.2 <;>
      simp [coloringMatrix, diagonalCount, hp]

/-- Equality of positive source products forces equality of diagonal counts;
therefore the exact product-collision condition for interpolation is proved. -/
theorem potts_coloring_compatible (q : ℕ) :
    Compatible (fun p : Fin q × Fin q => positivePottsMatrix q p.1 p.2)
      (fun p => coloringMatrix q p.1 p.2) := by
  intro xs ys _ _ _ heq
  rw [potts_product, potts_product] at heq
  have hc : diagonalCount xs=diagonalCount ys :=
    pow_right_injective₀ (by norm_num : (0:ℚ)<2) (by norm_num : (2:ℚ)≠1) heq
  rw [coloring_product, coloring_product, hc]

def noUnaries (q : ℕ) : Fin 0 → Fin q → ℚ := fun i => i.elim0

def coloringProblem {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ ℚ) (q : ℕ) : PromiseProblem :=
  evaluationProblem basis (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1)

def pottsProblem {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ ℚ) (q : ℕ) : PromiseProblem :=
  evaluationProblem basis (fun _ : Fin 1 => positivePottsMatrix q) (noUnaries q) (fun _ => 1)

/-- Actual ordinary-planar promised TM2 reduction, including empty graphs,
isolates, loops and repeated edge occurrences. No hardness premise is required. -/
def reduction {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ ℚ) (q : ℕ) :
    PromisePolyTimeTuringReduction (coloringProblem basis q) (pottsProblem basis q) := by
  apply binaryProductReduction basis (fun _ : Fin 1 => positivePottsMatrix q)
    (fun _ : Fin 1 => coloringMatrix q) (noUnaries q) (fun _ => 1) 0
  · intro l hl
    exact (hl (by simp [Subsingleton.elim l 0])).elim
  · intro i j hz
    by_cases he : i=j <;> simp [positivePottsMatrix,he] at hz
  · exact hasProductMaps_of_compatible _ _ (potts_coloring_compatible q)

/-- The representation is fixed explicitly and is not a cost-free rational oracle. -/
def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ

/-- The exact three-state planar source gate. This is a proved reduction, not
an assertion that its source is #P-hard. -/
def threeStateReduction :
    PromisePolyTimeTuringReduction (coloringProblem rationalBasis 3) (pottsProblem rationalBasis 3) :=
  reduction rationalBasis 3

/-- Exact counts of assignments satisfying every occurrence's inequality. -/
def properColoringCount {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (q : ℕ) : ℕ :=
  Fintype.card {σ : V → Fin q // ∀ e, σ (G.src e) ≠ σ (G.dst e)}

/-- The source oracle really returns the natural number of proper colorings. -/
theorem partition_eq_properColoringCount {V E : Type} [Fintype V] [Fintype E]
    (G : MultiGraph V E) (q : ℕ) :
    G.partition (coloringMatrix q) (fun _ => 1) = (properColoringCount G q : ℚ) := by
  unfold MultiGraph.partition MultiGraph.assignmentWeight
  simp only [Finset.prod_const_one, one_mul]
  have hp (σ : V → Fin q) : (∏ e, coloringMatrix q (σ (G.src e)) (σ (G.dst e))) =
      if ∀ e, σ (G.src e) ≠ σ (G.dst e) then (1:ℚ) else 0 := by
    by_cases h : ∀ e, σ (G.src e) ≠ σ (G.dst e)
    · simp [coloringMatrix,h]
    · obtain ⟨e, he⟩ := not_forall.mp h
      have heq : σ (G.src e)=σ (G.dst e) := not_ne_iff.mp he
      rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp [coloringMatrix,heq])]
      simp [h]
  simp_rw [hp]
  simp [properColoringCount, Fintype.card_subtype]

end PlanarHom.ProperColoringPottsReduction
