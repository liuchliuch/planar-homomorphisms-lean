import PlanarHom.CubeDirections
import Mathlib.Combinatorics.SimpleGraph.Prod

/-!
# Actual graph distance on the Boolean Cartesian cube

The graph metric is the number of differing coordinates. Its distance kernel
is therefore the literal Ising tensor with the same parameter in every factor.
-/

noncomputable section
open scoped BigOperators
namespace PlanarHom.Boolean

/-- The actual Cartesian product of two-point complete graphs. -/
def cubeGraph (d : ℕ) : SimpleGraph (Cube d) :=
  CartesianGeometry.hammingGraph (fun _ : Fin d => Bool)

/-- A graph homomorphism cannot increase extended graph distance. -/
theorem graphHom_edist_le {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (f : G →g H) (v w : V) : H.edist (f v) (f w) ≤ G.edist v w := by
  by_cases hr : G.Reachable v w
  · obtain ⟨p, hp⟩ := hr.exists_walk_length_eq_edist
    rw [← hp]
    simpa only [SimpleGraph.Walk.length_map] using SimpleGraph.edist_le (p.map f)
  · rw [SimpleGraph.edist_eq_top_of_not_reachable hr]
    exact le_top

/-- Isomorphisms preserve actual extended graph distance. -/
theorem graphIso_edist_eq {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (v w : V) : G.edist v w = H.edist (e v) (e w) := by
  apply le_antisymm
  · simpa using graphHom_edist_le e.symm.toHom (e v) (e w)
  · exact graphHom_edist_le e.toHom v w

/-- The cube graph has exactly the Hamming extended distance, including dimension zero. -/
theorem cubeGraph_edist {d : ℕ} (z w : Cube d) :
    (cubeGraph d).edist z w = ((∑ r : Fin d, if z r = w r then 0 else 1 : ℕ) : ℕ∞) := by
  induction d with
  | zero =>
    have he : z = w := Subsingleton.elim _ _
    subst w
    simp [SimpleGraph.edist_self]
  | succ d ih =>
    let e := CartesianGeometry.hammingGraph_finSucc (fun _ : Fin (d + 1) => Bool)
    have he := graphIso_edist_eq e z w
    change (cubeGraph (d + 1)).edist z w = _ at he
    rw [he, SimpleGraph.edist_boxProd, SimpleGraph.edist_top]
    change (if z 0 = w 0 then (0 : ℕ∞) else 1) +
      (cubeGraph d).edist (fun r => z r.succ) (fun r => w r.succ) = _
    rw [ih, Fin.sum_univ_succ, Nat.cast_add]
    by_cases h : z 0 = w 0 <;> simp [h]

/-- Ordinary natural graph distance is the number of differing coordinates. -/
theorem cubeGraph_dist {d : ℕ} (z w : Cube d) :
    (cubeGraph d).dist z w = ∑ r : Fin d, if z r = w r then 0 else 1 := by
  unfold SimpleGraph.dist
  rw [cubeGraph_edist]
  exact ENat.toNat_coe _

/-- The Boolean Cartesian graph is connected in every dimension. -/
theorem cubeGraph_connected (d : ℕ) : (cubeGraph d).Connected := by
  refine ⟨fun z w => SimpleGraph.reachable_of_edist_ne_top ?_⟩
  rw [cubeGraph_edist]
  exact ENat.coe_ne_top _

/-- The graph-distance kernel is the actual coordinate tensor, rather than a
separately assumed tensor representation. -/
theorem cubeGraph_distanceKernel_eq_tensor {d : ℕ} (x : ℝ) :
    EntropyCompletion.distanceKernel (cubeGraph d) x = tensor (fun _ => x) := by
  ext z w
  change x ^ (cubeGraph d).dist z w = ∏ r, if z r = w r then 1 else x
  rw [cubeGraph_dist, ← Finset.prod_pow_eq_pow_sum]
  apply Finset.prod_congr rfl
  intro r _
  by_cases h : z r = w r <;> simp [h]

end PlanarHom.Boolean
