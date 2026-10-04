import PlanarHom.Boolean
import Mathlib.Tactic.Linarith

/-!
# Affine functions on the Boolean cube

The vanishing of every mixed second difference forces a real-valued function on
`Fin d → Bool` to be affine in the individual bits. This is the finite algebraic
implication used in the proof of Proposition 4.8; no graph-theoretic or
complexity-theoretic claim is made here.
-/

noncomputable section

namespace PlanarHom.Boolean

open scoped BigOperators

/-- The cube vertex whose true coordinates form the given finite set. -/
private def vertexOfSet {d : ℕ} (S : Finset (Fin d)) : Cube d :=
  fun i => decide (i ∈ S)

private theorem vertexOfSet_empty {d : ℕ} :
    vertexOfSet (∅ : Finset (Fin d)) = (fun _ => false) := by
  funext i
  simp [vertexOfSet]

private theorem vertexOfSet_insert {d : ℕ} (S : Finset (Fin d))
    (r : Fin d) (hr : r ∉ S) :
    vertexOfSet (insert r S) = xor (vertexOfSet S) (unitBit r) := by
  funext i
  by_cases hi : i = r
  · subst i
    simp [vertexOfSet, xor, unitBit, hr]
  · simp [vertexOfSet, xor, unitBit, hi]

private theorem xor_zero_unitBit {d : ℕ} (r : Fin d) :
    xor (fun _ => false) (unitBit r) = unitBit r := by
  funext i
  simp [xor]

private theorem flip_comm {d : ℕ} (z : Cube d) (r s : Fin d) :
    xor (xor z (unitBit r)) (unitBit s) =
      xor (xor z (unitBit s)) (unitBit r) := by
  funext i
  simp only [xor]
  cases z i <;> cases unitBit r i <;> cases unitBit s i <;> rfl

/-- If all mixed second differences vanish, the change from turning on one bit
is independent of the other bits. The helper is stated on finite sets of true
coordinates, so the proof is finite induction. -/
private theorem single_difference_constant {d : ℕ} (φ : Cube d → ℝ)
    (h : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      φ z + φ (xor (xor z (unitBit r)) (unitBit s)) -
        φ (xor z (unitBit r)) - φ (xor z (unitBit s)) = 0)
    (r : Fin d) (S : Finset (Fin d)) (hr : r ∉ S) :
    φ (xor (vertexOfSet S) (unitBit r)) - φ (vertexOfSet S) =
      φ (unitBit r) - φ (fun _ => false) := by
  induction S using Finset.induction_on with
  | empty => simp only [vertexOfSet_empty, xor_zero_unitBit]
  | @insert s S hs ih =>
    have hrs : r ≠ s := by
      intro hrs
      subst s
      exact hr (Finset.mem_insert_self r S)
    have hrS : r ∉ S := fun hmem => hr (Finset.mem_insert_of_mem hmem)
    have hsq := h (vertexOfSet S) r s hrs
    rw [vertexOfSet_insert S s hs, ← flip_comm (vertexOfSet S) r s]
    have hbase := ih hrS
    linarith

/-- The mixed-difference step in Proposition 4.8: vanishing mixed second
Boolean differences gives the affine expansion, with coefficients determined
by the zero vertex and the unit vertices. This includes dimension zero. -/
theorem affine_of_mixedDifference_eq_zero {d : ℕ} (φ : Cube d → ℝ)
    (h : ∀ (z : Cube d) (r s : Fin d), r ≠ s →
      φ z + φ (xor (xor z (unitBit r)) (unitBit s)) -
        φ (xor z (unitBit r)) - φ (xor z (unitBit s)) = 0)
    (z : Cube d) :
    φ z = φ (fun _ => false) +
      ∑ r, (φ (unitBit r) - φ (fun _ => false)) * (if z r then 1 else 0) := by
  have hset (S : Finset (Fin d)) :
      φ (vertexOfSet S) = φ (fun _ => false) +
        ∑ r ∈ S, (φ (unitBit r) - φ (fun _ => false)) := by
    induction S using Finset.induction_on with
    | empty => simp only [vertexOfSet_empty, Finset.sum_empty, add_zero]
    | @insert r S hr ih =>
      rw [vertexOfSet_insert S r hr, Finset.sum_insert hr]
      have hd := single_difference_constant φ h r S hr
      linarith
  let S : Finset (Fin d) := Finset.univ.filter (fun i => z i = true)
  have hz : vertexOfSet S = z := by
    funext i
    simp [vertexOfSet, S]
  rw [← hz, hset]
  congr 1
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i _
  cases hzi : z i <;> simp [S, vertexOfSet, hzi]

end PlanarHom.Boolean
