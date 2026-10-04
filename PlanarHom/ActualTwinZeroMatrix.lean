import PlanarHom.RootedHomogeneousSemantics

/-!
# The zero-matrix case of actual twin removal

The value of a zero interaction is zero as soon as an edge (including a loop)
is present. Every edgeless input has one independent weight sum per vertex;
the empty input has value one, including when the color set is empty.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph

variable {V E C R : Type*} [Fintype V] [Fintype E] [Fintype C] [CommSemiring R]

/-- Complete zero-interaction formula, distinguishing edges from isolated
vertices rather than discarding either. -/
theorem partition_zeroMatrix (G : MultiGraph V E) (w : C → R) :
    G.partition (0 : Matrix C C R) w =
      if Nonempty E then 0 else (∑ i, w i) ^ Fintype.card V := by
  by_cases he : Nonempty E
  · letI := he
    simpa only [he, ↓reduceIte] using G.partition_zero_of_nonempty_edges w
  · letI : IsEmpty E := ⟨fun e => he ⟨e⟩⟩
    simpa only [he, ↓reduceIte] using G.partition_edgeless (0 : Matrix C C R) w

end PlanarHom.MultiGraph

namespace PlanarHom.Complexity.MixedCode

variable {C R : Type} [Fintype C] [CommSemiring R]

/-- A raw valid one-label input has the same explicit zero-matrix formula. -/
theorem evaluate_zeroMatrix (g : MixedCode) (hg : g.Valid 1 0) (w : C → R) :
    g.evaluate hg (fun _ : Fin 1 => (0 : Matrix C C R))
      (fun u : Fin 0 => Fin.elim0 u) w =
      if g.edges ≠ [] then 0 else (∑ i, w i) ^ g.vertices := by
  rw [evaluate_homogeneous, MultiGraph.partition_zeroMatrix]
  have he : Nonempty (Fin g.edges.length) ↔ g.edges ≠ [] := by
    rw [← List.length_pos_iff_ne_nil]
    constructor
    · rintro ⟨i⟩
      exact Nat.zero_lt_of_lt i.isLt
    · intro h
      exact ⟨⟨0, h⟩⟩
  simp only [he, Fintype.card_fin]

/-- The total source oracle agrees with the explicit formula on valid inputs. -/
theorem totalEvaluation_zeroMatrix (g : MixedCode) (hg : g.Valid 1 0) (w : C → R) :
    totalEvaluation (fun _ : Fin 1 => (0 : Matrix C C R))
      (fun u : Fin 0 => Fin.elim0 u) w g =
      if g.edges ≠ [] then 0 else (∑ i, w i) ^ g.vertices := by
  rw [totalEvaluation_valid _ _ _ _ hg]
  exact evaluate_zeroMatrix g hg w

/-- With no vertices, validity forces the edge list to be empty. -/
theorem edges_nil_of_valid_vertices_zero (g : MixedCode) (hg : g.Valid 1 0)
    (hv : g.vertices = 0) : g.edges = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have h := (hg.1 e he).1
  rw [hv] at h
  exact Nat.not_lt_zero _ h

/-- In particular, the zero-matrix oracle preserves the empty assignment. -/
theorem evaluate_zeroMatrix_of_vertices_zero (g : MixedCode) (hg : g.Valid 1 0)
    (hv : g.vertices = 0) (w : C → R) :
    g.evaluate hg (fun _ : Fin 1 => (0 : Matrix C C R))
      (fun u : Fin 0 => Fin.elim0 u) w = 1 := by
  rw [evaluate_zeroMatrix, edges_nil_of_valid_vertices_zero g hg hv, hv]
  simp

theorem totalEvaluation_zeroMatrix_of_vertices_zero (g : MixedCode) (hg : g.Valid 1 0)
    (hv : g.vertices = 0) (w : C → R) :
    totalEvaluation (fun _ : Fin 1 => (0 : Matrix C C R))
      (fun u : Fin 0 => Fin.elim0 u) w g = 1 := by
  rw [totalEvaluation_valid _ _ _ _ hg]
  exact evaluate_zeroMatrix_of_vertices_zero g hg hv w

end PlanarHom.Complexity.MixedCode
