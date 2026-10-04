import PlanarHom.PlanarRadialTails
import Mathlib.Tactic.FieldSimp

/-!
# Affine normalization of a plane segment

An explicit affine homeomorphism sends the second endpoint to the origin and
the first endpoint to `(1,0)`. It preserves real affine combinations, hence
segments and all rays based at the second endpoint.
-/

noncomputable section
open Set
open scoped Convex
namespace PlanarHom.MultiGraph

private theorem segment_normSq_ne_zero (a b : Plane) (hab : a ≠ b) :
    (a.1-b.1)^2 + (a.2-b.2)^2 ≠ 0 := by
  intro h
  have hx : a.1 = b.1 := by nlinarith [sq_nonneg (a.1-b.1),sq_nonneg (a.2-b.2)]
  have hy : a.2 = b.2 := by nlinarith [sq_nonneg (a.1-b.1),sq_nonneg (a.2-b.2)]
  exact hab (Prod.ext hx hy)

/-- Normalize a nondegenerate segment, with the second endpoint as center. -/
def normalizeSegment (a b : Plane) (hab : a ≠ b) : Plane ≃ₜ Plane where
  toFun x :=
    (((x.1-b.1)*(a.1-b.1) + (x.2-b.2)*(a.2-b.2)) /
      ((a.1-b.1)^2 + (a.2-b.2)^2),
     ((a.1-b.1)*(x.2-b.2) - (a.2-b.2)*(x.1-b.1)) /
      ((a.1-b.1)^2 + (a.2-b.2)^2))
  invFun y :=
    (b.1 + (a.1-b.1)*y.1 - (a.2-b.2)*y.2,
     b.2 + (a.2-b.2)*y.1 + (a.1-b.1)*y.2)
  left_inv := by
    intro x
    have hn := segment_normSq_ne_zero a b hab
    apply Prod.ext <;> dsimp <;> field_simp <;> nlinarith [hn]
  right_inv := by
    intro y
    have hn := segment_normSq_ne_zero a b hab
    apply Prod.ext <;> dsimp <;> field_simp <;> ring
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

/-- Coordinate formula for the inverse affine normalization. -/
theorem normalizeSegment_symm_apply (a b : Plane) (hab : a ≠ b) (y : Plane) :
    (normalizeSegment a b hab).symm y =
      (b.1 + (a.1-b.1)*y.1 - (a.2-b.2)*y.2,
       b.2 + (a.2-b.2)*y.1 + (a.1-b.1)*y.2) := rfl

@[simp] theorem normalizeSegment_center (a b : Plane) (hab : a ≠ b) :
    normalizeSegment a b hab b = (0,0) := by
  simp [normalizeSegment]

@[simp] theorem normalizeSegment_endpoint (a b : Plane) (hab : a ≠ b) :
    normalizeSegment a b hab a = (1,0) := by
  have hn := segment_normSq_ne_zero a b hab
  apply Prod.ext
  · change ((a.1-b.1)*(a.1-b.1) + (a.2-b.2)*(a.2-b.2)) /
      ((a.1-b.1)^2 + (a.2-b.2)^2) = 1
    convert div_self hn using 1; ring
  · change ((a.1-b.1)*(a.2-b.2) - (a.2-b.2)*(a.1-b.1)) /
      ((a.1-b.1)^2 + (a.2-b.2)^2) = 0
    rw [show (a.1-b.1)*(a.2-b.2) - (a.2-b.2)*(a.1-b.1) = 0 by ring,zero_div]

@[simp] theorem normalizeSegment_symm_center (a b : Plane) (hab : a ≠ b) :
    (normalizeSegment a b hab).symm (0,0) = b := by
  apply (normalizeSegment a b hab).injective
  simp

@[simp] theorem normalizeSegment_symm_endpoint (a b : Plane) (hab : a ≠ b) :
    (normalizeSegment a b hab).symm (1,0) = a := by
  apply (normalizeSegment a b hab).injective
  simp

/-- Normalization preserves every real ray parameter based at its center. -/
theorem normalizeSegment_ray (a b : Plane) (hab : a ≠ b) (t : ℝ) (c : Plane) :
    normalizeSegment a b hab (b + t • (c-b)) = t • normalizeSegment a b hab c := by
  apply Prod.ext <;> dsimp [normalizeSegment] <;> ring

/-- Inverse normalization sends rays at the origin to rays at the chosen center. -/
theorem normalizeSegment_symm_ray (a b : Plane) (hab : a ≠ b) (t : ℝ) (c : Plane) :
    (normalizeSegment a b hab).symm (t • c) =
      b + t • ((normalizeSegment a b hab).symm c-b) := by
  apply (normalizeSegment a b hab).injective
  simp only [Homeomorph.apply_symm_apply,normalizeSegment_ray]

/-- Normalization commutes with affine interpolation. -/
theorem normalizeSegment_lineMap (a b : Plane) (hab : a ≠ b) (x y : Plane) (t : ℝ) :
    normalizeSegment a b hab (AffineMap.lineMap x y t) =
      AffineMap.lineMap (normalizeSegment a b hab x) (normalizeSegment a b hab y) t := by
  simp only [AffineMap.lineMap_apply_module]
  apply Prod.ext <;> dsimp [normalizeSegment] <;> ring

/-- Every segment maps onto the segment between its normalized endpoints. -/
theorem normalizeSegment_image_segment (a b : Plane) (hab : a ≠ b) (x y : Plane) :
    normalizeSegment a b hab '' [x -[ℝ] y] =
      [normalizeSegment a b hab x -[ℝ] normalizeSegment a b hab y] := by
  rw [segment_eq_image_lineMap,segment_eq_image_lineMap,Set.image_image]
  congr 1
  funext t
  exact normalizeSegment_lineMap a b hab x y t

/-- The preimage of a normalized segment is the original segment. -/
theorem normalizeSegment_preimage_segment (a b : Plane) (hab : a ≠ b) (x y : Plane) :
    normalizeSegment a b hab ⁻¹'
      [normalizeSegment a b hab x -[ℝ] normalizeSegment a b hab y] = [x -[ℝ] y] := by
  rw [← normalizeSegment_image_segment]
  exact Set.preimage_image_eq _ (normalizeSegment a b hab).injective

/-- The chosen segment maps onto the horizontal unit segment. -/
theorem normalizeSegment_image (a b : Plane) (hab : a ≠ b) :
    normalizeSegment a b hab '' [b -[ℝ] a] = [(0,0) -[ℝ] (1,0)] := by
  rw [normalizeSegment_image_segment,normalizeSegment_center,normalizeSegment_endpoint]

/-- The horizontal unit segment has precisely the chosen segment as preimage. -/
theorem normalizeSegment_preimage (a b : Plane) (hab : a ≠ b) :
    normalizeSegment a b hab ⁻¹' [(0,0) -[ℝ] (1,0)] = [b -[ℝ] a] := by
  rw [← normalizeSegment_center a b hab,← normalizeSegment_endpoint a b hab]
  exact normalizeSegment_preimage_segment a b hab b a

end PlanarHom.MultiGraph
