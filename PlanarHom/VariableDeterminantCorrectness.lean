import PlanarHom.VariableDeterminantProgram

/-! NEW: exact determinant semantics for every raw square/ragged list and every
finite matrix. No nonsingularity, positivity, or bounded-order premise. -/
noncomputable section
open Classical
namespace PlanarHom.VariableDeterminant
open PfaffianList BlockPfaffian
attribute [-simp] Fin.natAdd_eq_addNat
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)

theorem range_map_eq_ofFn {A : Type} (n : ℕ) (f : ℕ → A) :
    (List.range n).map f = List.ofFn (fun i : Fin n => f i.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp

def rawMatrix (g : Grid K) : Matrix (Fin g.length) (Fin g.length) K :=
  fun i j => entry g i.val j.val

theorem blockGrid_eq_matrixRows (g : Grid K) :
    blockGrid g = matrixRows (block (rawMatrix g)) := by
  have hc {n m : ℕ} (h : n ≤ n + m) (i : Fin n) :
      Fin.castLE h i = Fin.castAdd m i := rfl
  simp [blockGrid, rows, range_map_eq_ofFn, upperRow, lowerRow, zeroRow,
    rawMatrix, matrixRows, List.ofFn_add, hc]


theorem identityGrid_eq_matrixRows (g : Grid K) :
    identityGrid g = matrixRows (1 : Matrix (Fin g.length) (Fin g.length) K) := by
  simp only [identityGrid, rows, matrixRows, range_map_eq_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  simp [Matrix.one_apply, Fin.ext_iff]

@[simp] theorem rawMatrix_matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    rawMatrix (matrixRows A) = fun i j => A (Fin.cast (matrixRows_length A) i)
      (Fin.cast (matrixRows_length A) j) := by
  ext i j
  exact entry_matrixRows A (Fin.cast (matrixRows_length A) i) (Fin.cast (matrixRows_length A) j)

theorem blockGrid_matrixRows {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    blockGrid (matrixRows A) = matrixRows (block A) := by
  have hc {n m : ℕ} (h : n ≤ n + m) (i : Fin n) :
      Fin.castLE h i = Fin.castAdd m i := rfl
  simp [blockGrid, rows, range_map_eq_ofFn, upperRow, lowerRow, zeroRow,
    matrixRows, List.ofFn_add, hc, entry, lookup]

include basis in
theorem determinant_eq_det (g : Grid K) : determinant g = (rawMatrix g).det := by
  have hcal : evaluateGrid (blockGrid (identityGrid g)) =
      MultiGraph.pairingPfaffian (block (1 : Matrix (Fin g.length) (Fin g.length) K)) := by
    rw [identityGrid_eq_matrixRows, blockGrid_matrixRows]
    exact evaluateGrid_matrixRows basis _ (block_skew _) (block_diag _)
  unfold determinant
  rw [hcal, blockGrid_eq_matrixRows,
    evaluateGrid_matrixRows basis _ (block_skew _) (block_diag _)]
  exact (determinant_eq_calibrated_pfaffian (rawMatrix g)).symm

include basis in
/-- Exact original determinant for every runtime dimension, including zero. -/
theorem determinant_ofFn {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    determinant (List.ofFn (fun i => List.ofFn (A i))) = A.det := by
  change determinant (matrixRows A) = _
  rw [determinant_eq_det basis, rawMatrix_matrixRows]
  exact Matrix.det_submatrix_equiv_self (finCongr (matrixRows_length A)) A

attribute [simp] Fin.natAdd_eq_addNat

end PlanarHom.VariableDeterminant
