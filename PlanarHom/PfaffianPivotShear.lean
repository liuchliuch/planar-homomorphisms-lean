import PlanarHom.PfaffianEliminationHeights
import PlanarHom.OccurrencePfaffianVertexLinearity

/-! Algebraic assembly of pivot isolation by elementary vertex shears. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
variable {V F : Type*} [LinearOrder V] [Field F]

/-- Simultaneously add multiples of one source row and the same multiples of
its source column. The quadratic term vanishes for alternating matrices. -/
def sourceShear (A : Matrix V V F) (source : V) (c : V → F) : Matrix V V F :=
  fun u v => A u v + c u * A source v + c v * A u source

/-- The elementary simultaneous row/column addition. -/
def elementaryShear (A : Matrix V V F) (source target : V) (c : F) : Matrix V V F :=
  fun u v => A u v + (if u=target then c*A source v else 0) +
    (if v=target then c*A u source else 0)

/-- A finite set of target shears with fixed original coefficients. -/
def partialSourceShear (A : Matrix V V F) (source : V) (T : Finset V) (c : V → F) : Matrix V V F :=
  sourceShear A source (fun u => if u∈T then c u else 0)

theorem sourceShear_skew (A : Matrix V V F) (source : V) (c : V → F)
    (hA : ∀ u v, A v u = -A u v) : ∀ u v,
    sourceShear A source c v u = -sourceShear A source c u v := by
  intro u v
  simp only [sourceShear, hA u v, hA source u, hA source v]
  ring

theorem sourceShear_diag (A : Matrix V V F) (source : V) (c : V → F)
    (hA : ∀ u v, A v u = -A u v) (hdiag : ∀ u, A u u=0) : ∀ u,
    sourceShear A source c u u = 0 := by
  intro u
  simp only [sourceShear, hdiag u, hA source u]
  ring

theorem partialSourceShear_empty (A : Matrix V V F) (source : V) (c : V → F) :
    partialSourceShear A source ∅ c = A := by
  ext u v
  simp [partialSourceShear, sourceShear]

/-- Distinct target shears commute and add their coefficients exactly. -/
theorem partialSourceShear_insert (A : Matrix V V F) (source target : V)
    (T : Finset V) (c : V → F) (ht : target ∉ T) (hs : source ∉ T)
    (hdiag : A source source=0) :
    partialSourceShear A source (insert target T) c =
      elementaryShear (partialSourceShear A source T c) source target (c target) := by
  ext u v
  by_cases hu : u=target <;> by_cases hv : v=target <;>
    simp [partialSourceShear, sourceShear, elementaryShear, hu, hv, ht, hs, hdiag]
  <;> ring

/-- Coefficients eliminating every first-row entry except the selected pivot. -/
def pivotShearCoefficient (A : Matrix V V F) (i j : V) (u : V) : F :=
  if u=i ∨ u=j then 0 else -A i u / A i j

def pivotIsolated (A : Matrix V V F) (i j : V) : Matrix V V F :=
  sourceShear A j (pivotShearCoefficient A i j)

@[simp] theorem pivotIsolated_pivot (A : Matrix V V F) (i j : V) :
    pivotIsolated A i j i j = A i j := by
  simp [pivotIsolated, sourceShear, pivotShearCoefficient]

theorem pivotIsolated_zero_row (A : Matrix V V F) (i j : V) (hp : A i j ≠0)
    {v : V} (hvi : v≠i) (hvj : v≠j) : pivotIsolated A i j i v = 0 := by
  simp only [pivotIsolated, sourceShear, pivotShearCoefficient, hvi, hvj,
    false_or, ↓reduceIte, true_or, zero_mul, add_zero]
  field_simp
  <;> ring

/-- The residual block after genuine pivot isolation is the exact program update. -/
theorem pivotIsolated_residual (A : Matrix V V F) (i j : V)
    (hskew : ∀ u v, A v u = -A u v) (u v : V)
    (hui : u≠i) (huj : u≠j) (hvi : v≠i) (hvj : v≠j) :
    pivotIsolated A i j u v =
      A u v - A i u * A j v / A i j + A j u * A i v / A i j := by
  simp only [pivotIsolated, sourceShear, pivotShearCoefficient, hui,huj,hvi,hvj,
    false_or, ↓reduceIte, hskew j u, div_eq_mul_inv]
  ring

/-- Restricting the simultaneous shears to active targets changes no semantic
entry of the supported Pfaffian. -/
theorem partialSourceShear_active_congr [Fintype V] (S : Finset V)
    (A : Matrix V V F) (i j : V) :
    supportedPfaffian S (partialSourceShear A j (S.erase j) (pivotShearCoefficient A i j)) =
      supportedPfaffian S (pivotIsolated A i j) := by
  apply supportedPfaffian_congr
  intro u hu v hv _
  by_cases huj : u=j <;> by_cases hvj : v=j <;>
    simp [partialSourceShear, sourceShear, pivotIsolated, pivotShearCoefficient, huj, hvj, hu, hv]

/-- Once invariance under the pivot-isolating congruence has been established,
the remaining semantic step is exactly the existing literal Laplace expansion. -/
theorem supportedPfaffian_pivotIsolated [Fintype V]
    (S : Finset V) (A : Matrix V V F) (i j : V)
    (hi : i∈S) (hj : j∈S) (hij : i<j) (hmin : ∀ v∈S, i≤v)
    (hskew : ∀ u v, A v u = -A u v) (hp : A i j≠0) :
    supportedPfaffian S (pivotIsolated A i j) =
      (-1:F)^(S.filter (fun v => i<v ∧ v<j)).card * A i j *
        supportedPfaffian ((S.erase i).erase j)
          (fun u v => A u v - A i u*A j v/A i j + A j u*A i v/A i j) := by
  rw [supportedPfaffian_single_pivot_row S (pivotIsolated A i j) i j hi hj hij hmin
    (fun v _ hiv hvj => pivotIsolated_zero_row A i j hp hiv.ne' hvj), pivotIsolated_pivot]
  congr 1
  apply supportedPfaffian_congr
  intro u hu v hv _
  exact pivotIsolated_residual A i j hskew u v
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hu)).1 (Finset.mem_erase.mp hu).1
    (Finset.mem_erase.mp (Finset.mem_of_mem_erase hv)).1 (Finset.mem_erase.mp hv).1

end PlanarHom.MultiGraph
