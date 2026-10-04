import PlanarHom.GraphDegreeMachines
import Mathlib.Data.Fintype.Fin

/-! The compiled endpoint-counting program computes the occurrence-based
multigraph degree, with both incidences of every loop. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.GraphDegreeMachines
open Complexity Complexity.MixedCode

theorem degree_sum (g : MixedCode) (v : ℕ) :
    degree g v=(g.edges.map (fun e=>(if e.1=v then 1 else 0)+(if e.2.1=v then 1 else 0))).sum := by
  unfold degree endpoints
  induction g.edges with
  | nil => simp
  | cons e es ih =>
    by_cases h1:e.1=v <;> by_cases h2:e.2.1=v <;>
      simp [List.flatMap_cons,h1,h2,ih,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] <;> omega

theorem degree_toMultiGraph (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (v : Fin g.vertices) :
    degree g v.val=(g.toMultiGraph hg).degree v := by
  rw [degree_sum,MultiGraph.degree,Finset.card_filter,Finset.card_filter,←Finset.sum_add_distrib]
  rw [←Fin.sum_univ_fun_getElem]
  apply Finset.sum_congr rfl
  intro e _
  simp [toMultiGraph,Fin.ext_iff,List.get_eq_getElem]

/-- Product over the actual generated descending degree list is the same
vertex product; its ordering has no computational effect. -/
theorem prod_map_degrees {R : Type} [CommMonoid R] (g : MixedCode) (f : ℕ→R) :
    ((degrees g).map f).prod=∏v : Fin g.vertices,f (degree g v.val) := by
  simp only [degrees,List.map_map,List.map_reverse,List.prod_reverse]
  rw [←Fin.prod_univ_fun_getElem]
  apply Fintype.prod_equiv (finCongr (List.length_range (n:=g.vertices)))
  intro v
  simp [Function.comp_def,List.get_eq_getElem,List.getElem_range]

/-- The actual list evaluator has the proved rank-one partition semantics. -/
theorem rankOne_evaluate (g : MixedCode) (hg : g.Valid 1 0) {C R : Type}
    [Fintype C] [CommSemiring R] (a w : C→R) :
    g.evaluate hg (fun _ : Fin 1=>fun i j=>a i*a j) (fun i : Fin 0=>Fin.elim0 i) w =
      ((degrees g).map (fun n=>∑i,w i*a i^n)).prod := by
  rw [evaluate_homogeneous,MultiGraph.partition_rankOne,prod_map_degrees]
  apply Finset.prod_congr rfl
  intro v _
  rw [degree_toMultiGraph g hg v]

end PlanarHom.GraphDegreeMachines
