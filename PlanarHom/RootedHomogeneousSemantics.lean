import PlanarHom.RootedCodeNormalization
import PlanarHom.RootedRestrictionIdentity
import PlanarHom.MixedTotalEvaluation

/-! The actual one-label weighted source oracle has exactly the ordinary
multigraph value; rooted attachment queries retain one copy of each weight. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom.Complexity.MixedCode
variable {C R : Type} [Fintype C] [CommSemiring R]

theorem unaries_nil_of_valid_zero (g : MixedCode) (hg : g.Valid 1 0) : g.unaries = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  exact Nat.not_lt_zero _ (hg.2 u hu).2

theorem evaluate_homogeneous (g : MixedCode) (hg : g.Valid 1 0)
    (M : Matrix C C R) (w : C → R) :
    g.evaluate hg (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w =
      (g.toMultiGraph hg).partition M w := by
  unfold evaluate MultiGraph.partition MultiGraph.assignmentWeight
  rw [unaries_nil_of_valid_zero g hg]
  simp only [List.map_nil,List.prod_nil,mul_one]
  apply Finset.sum_congr
  · ext σ; simp
  intro σ _
  congr 1
  rw [← Fin.prod_univ_fun_getElem]
  apply Finset.prod_congr rfl
  intro e _
  have hv := hg.1 (g.edges.get e) (List.get_mem _ _)
  simp only [List.get_eq_getElem] at hv
  simp only [binaryValue,dif_pos hv,toMultiGraph,List.get_eq_getElem]

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.RootedRestriction
local instance (priority := 10000) rootedHomogeneousSemanticsDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
open Complexity Complexity.MixedCode
variable {C K : Type} [Fintype C] [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n m : ℕ}

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem attached_oracle_value (H : RootedGraph (Fin n) (Fin m))
    (g : MixedCode) (hg : g.Valid 1 0) (r : Fin g.vertices)
    (M : Matrix C C K) (w : C → K) :
    totalEvaluation (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w
      (RootedCodeMachines.attach H 0 (r.val,g)) =
        ((g.toMultiGraph hg).attachRooted H r).partition M w := by
  have hv := RootedCodeMachines.attach_valid H 0 (r.val,g) hg r.isLt (by decide : 0<1)
  rw [totalEvaluation_valid _ _ _ _ hv,evaluate_homogeneous]
  exact (RootedCodeMachines.attachIncidenceEquiv H 0 g hg r (by decide)).partition M w

/-- Fixed source-field coefficients recover the root-domain sum from the
literal queries emitted by the compiled rooted attachment program. -/
theorem exists_computed_root_queries (M : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (X : Set C) :
    ∃ k : ℕ, ∃ graphs : Fin k → FiniteRootedPlanar, ∃ c : Fin k → K,
      ∀ (g : MixedCode) (hg : g.PlanarValid 1 0) (r : Fin g.vertices),
        RootedGraph.restricted ((g.toMultiGraph hg.1).atRoot r) M w X =
          ∑ j, c j * totalEvaluation (fun _ : Fin 1 => M) (fun u : Fin 0 => Fin.elim0 u) w
            (RootedCodeMachines.attach (graphs j).2.2.val 0 (r.val,g)) := by
  obtain ⟨k,graphs,c,h⟩ := exists_attachment_coefficients M w hw X
  refine ⟨k,graphs,c,?_⟩
  intro g hg r
  rw [h _ _ (g.toMultiGraph hg.1) r ((planarValid_iff g hg.1).mp hg)]
  apply Finset.sum_congr rfl
  intro j _
  rw [attached_oracle_value]

end PlanarHom.RootedRestriction
