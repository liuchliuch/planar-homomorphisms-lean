import PlanarHom.OccurrencePfaffianExpansion
import PlanarHom.OccurrencePfaffianRegressions

/- NEW regression proofs for the reconstructed core. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
namespace ReconstructedPfaffianCoreRegression

/-- Empty dimension is the empty product, with value one. -/
theorem empty_pfaffian {R : Type*} [CommRing R] (A : Matrix (Fin 0) (Fin 0) R) :
    pairingPfaffian A = 1 := by
  rw [← supportedPfaffian_univ]
  have h : (Finset.univ : Finset (Fin 0)) = ∅ := Finset.univ_eq_empty
  rw [h, supportedPfaffian_empty]

/-- Odd dimension vanishes without assumptions on entries. -/
theorem odd_three_pfaffian {R : Type*} [CommRing R] (A : Matrix (Fin 3) (Fin 3) R) :
    pairingPfaffian A = 0 :=
  pairingPfaffian_eq_zero_of_odd (by exact ⟨1,rfl⟩) A

/-- A two-element active set works even when ambient indices are not adjacent. -/
theorem supported_pair {V R : Type*} [Fintype V] [LinearOrder V] [CommRing R]
    (i j : V) (hij : i < j) (A : Matrix V V R) :
    supportedPfaffian {i,j} A = A i j := by
  have hzero : ∀ k ∈ ({i,j} : Finset V), i < k → k ≠ j → A i k = 0 := by
    intro k hk hlt hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · exact (lt_irrefl _ hlt).elim
    · exact (hne rfl).elim
  have hmin : ∀ v ∈ ({i,j} : Finset V), i ≤ v := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact le_rfl
    · exact hij.le
  rw [supportedPfaffian_single_pivot_row _ A i j (by simp) (by simp) hij hmin hzero]
  have hfilter : (({i,j} : Finset V).filter (fun v => i < v ∧ v < j)) = ∅ := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, Finset.notMem_empty,
      iff_false, not_and]
    rintro (rfl | rfl) h₁ h₂
    · exact lt_irrefl _ h₁
    · exact lt_irrefl _ h₂
  rw [hfilter]
  simp [hij.ne]

theorem nonadjacent_support (A : Matrix (Fin 4) (Fin 4) ℤ) :
    supportedPfaffian {0,3} A = A 0 3 := supported_pair _ _ (by decide) A

/-- Minimum-row vanishing kills a nonempty supported Pfaffian. -/
theorem zero_first_row {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R)
    (h : ∀ j, A 0 j = 0) : pairingPfaffian A = 0 := by
  rw [← supportedPfaffian_univ]
  exact supportedPfaffian_zero_row _ A 0 (by simp) (by intro v _; exact Fin.zero_le v)
    (by intro j _ _; exact h j)

/-- Full Pfaffian expansion retains the usual crossing minus sign. -/
theorem four_vertex_formula {R : Type*} [CommRing R] (A : Matrix (Fin 4) (Fin 4) R) :
    pairingPfaffian A = A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2 := by
  rw [← supportedPfaffian_univ, supportedPfaffian_expand_min _ A 0 (by simp)
    (by intro v _; exact Fin.zero_le v)]
  classical
  change (∑ j : {j : Fin 4 // j ∈ Finset.univ ∧ (0 : Fin 4) < j},
    (-1 : R) ^ (Finset.univ.filter (fun v : Fin 4 => 0 < v ∧ v < j.val)).card *
      A 0 j.val * supportedPfaffian ((Finset.univ.erase 0).erase j.val) A) = _
  rw [← Finset.sum_subtype (Finset.univ.filter (fun j : Fin 4 => j ∈ Finset.univ ∧ (0 : Fin 4) < j)) (by simp)
    (fun j => (-1 : R) ^ (Finset.univ.filter (fun v : Fin 4 => 0 < v ∧ v < j)).card *
      A 0 j * supportedPfaffian ((Finset.univ.erase 0).erase j) A), Finset.sum_filter]
  have he1 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 1 = {2,3} := by decide
  have he2 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 2 = {1,3} := by decide
  have he3 : ((Finset.univ : Finset (Fin 4)).erase 0).erase 3 = {1,2} := by decide
  have hc1 : (Finset.univ.filter (fun v : Fin 4 => 0 < v ∧ v < 1)).card = 0 := by decide
  have hc2 : (Finset.univ.filter (fun v : Fin 4 => 0 < v ∧ v < 2)).card = 1 := by decide
  have hc3 : (Finset.univ.filter (fun v : Fin 4 => 0 < v ∧ v < 3)).card = 2 := by decide
  norm_num [Fin.sum_univ_succ, show Fin.succ (2 : Fin 3) = (3 : Fin 4) from rfl,
    he1, he2, he3, hc1, hc2, hc3,
    supported_pair (2 : Fin 4) 3 (by decide) A,
    supported_pair (1 : Fin 4) 3 (by decide) A,
    supported_pair (1 : Fin 4) 2 (by decide) A, sub_eq_add_neg]
  ring

end ReconstructedPfaffianCoreRegression
end PlanarHom.MultiGraph
