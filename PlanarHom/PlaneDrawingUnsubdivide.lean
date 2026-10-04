import PlanarHom.PolygonalSegmentIncidence

/-! Suppression of geometric midpoints joins the two actual edge curves.
No graph subdivision is left in the resulting partition-function instance. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.PlaneDrawing
variable {V E : Type*} {G : MultiGraph V E}

def leftPath (d : PlaneDrawing G.subdivide) (e : E) :
    Path (d.point (.inl (G.src e))) (d.point (.inr e)) where
  toContinuousMap := d.curve (e,false)
  source' := by simpa [MultiGraph.subdivide] using d.curve_zero (e,false)
  target' := by simpa [MultiGraph.subdivide] using d.curve_one (e,false)

def rightPath (d : PlaneDrawing G.subdivide) (e : E) :
    Path (d.point (.inr e)) (d.point (.inl (G.dst e))) where
  toContinuousMap := d.curve (e,true)
  source' := by simpa [MultiGraph.subdivide] using d.curve_zero (e,true)
  target' := by simpa [MultiGraph.subdivide] using d.curve_one (e,true)

def joinedPath (d : PlaneDrawing G.subdivide) (e : E) := (leftPath d e).trans (rightPath d e)

@[simp] theorem joined_half (d : PlaneDrawing G.subdivide) (e : E) (b : Bool) (t : I) :
    joinedPath d e (halfParameter b t)=d.curve (e,b) t := by
  cases b
  · exact Polygonal.trans_left_half (leftPath d e) (rightPath d e) t
  · exact Polygonal.trans_right_half (leftPath d e) (rightPath d e) t

@[simp] theorem joined_midpoint (d : PlaneDrawing G.subdivide) (e : E) :
    joinedPath d e half=d.point (.inr e) := by
  rw [←halfParameter_false_one,joined_half]
  simpa [MultiGraph.subdivide] using d.curve_one (e,false)

theorem inside_half_or_midpoint (t : I) (ht : Inside t) :
    t=half ∨ ∃ b s,Inside s ∧ halfParameter b s=t := by
  by_cases h : t=half
  · exact Or.inl h
  · right
    by_cases hl : (t:ℝ)<1/2
    · refine ⟨false,⟨2*(t:ℝ),by constructor <;> linarith [ht.1]⟩,?_,?_⟩
      · constructor <;> dsimp <;> linarith [ht.1]
      · apply Subtype.ext; dsimp [halfParameter]; ring
    · have hne : (t:ℝ)≠1/2 := fun hh => h (Subtype.ext hh)
      have hgt : (1/2:ℝ)<t := lt_of_le_of_ne (le_of_not_gt hl) (Ne.symm hne)
      refine ⟨true,⟨2*(t:ℝ)-1,by constructor <;> linarith [ht.2]⟩,?_,?_⟩
      · constructor <;> dsimp <;> linarith [ht.2]
      · apply Subtype.ext; dsimp [halfParameter]; ring

/-- Actual inverse subdivision: retain original vertices and concatenate each
pair of curves. This also permits loops and parallel original occurrences. -/
def unsubdivide (d : PlaneDrawing G.subdivide) : PlaneDrawing G where
  point v := d.point (.inl v)
  point_injective := by intro v w h; exact Sum.inl.inj (d.point_injective h)
  curve e := (joinedPath d e).toContinuousMap
  curve_zero e := (joinedPath d e).source
  curve_one e := (joinedPath d e).target
  interior_injective e f s t hs ht h := by
    change joinedPath d e s=joinedPath d f t at h
    rcases inside_half_or_midpoint s hs with rfl | ⟨b,u,hu,rfl⟩
    · rcases inside_half_or_midpoint t ht with rfl | ⟨c,v,hv,rfl⟩
      · rw [joined_midpoint,joined_midpoint] at h
        exact ⟨Sum.inr.inj (d.point_injective h),rfl⟩
      · rw [joined_midpoint,joined_half] at h
        exact False.elim (d.interior_avoids (f,c) v hv (.inr e) h.symm)
    · rcases inside_half_or_midpoint t ht with rfl | ⟨c,v,hv,rfl⟩
      · rw [joined_half,joined_midpoint] at h
        exact False.elim (d.interior_avoids (e,b) u hu (.inr f) h)
      · rw [joined_half,joined_half] at h
        obtain ⟨hef,huv⟩ := d.interior_injective (e,b) (f,c) u v hu hv h
        have he := congrArg Prod.fst hef
        have hb := congrArg Prod.snd hef
        dsimp only at he hb
        subst f; subst c; subst v
        exact ⟨rfl,rfl⟩
  interior_avoids e t ht v h := by
    change joinedPath d e t=d.point (.inl v) at h
    rcases inside_half_or_midpoint t ht with rfl | ⟨b,s,hs,rfl⟩
    · rw [joined_midpoint] at h
      exact Sum.noConfusion (d.point_injective h)
    · rw [joined_half] at h
      exact d.interior_avoids (e,b) s hs (.inl v) h

/-- Interior containment passes through the suppressed geometric midpoint. -/
theorem unsubdivide_curve_in (d : PlaneDrawing G.subdivide) (U : Set Plane)
    (hmid : ∀e,d.point (.inr e)∈U)
    (hcurve : ∀e b t,Inside t→d.curve (e,b) t∈U) :
    ∀e t,Inside t→d.unsubdivide.curve e t∈U := by
  intro e t ht
  change joinedPath d e t∈U
  rcases inside_half_or_midpoint t ht with rfl | ⟨b,s,hs,rfl⟩
  · rw [joined_midpoint]; exact hmid e
  · rw [joined_half]; exact hcurve e b s hs

end PlanarHom.MultiGraph.PlaneDrawing
