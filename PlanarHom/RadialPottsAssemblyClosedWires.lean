import PlanarHom.RadialPottsAssemblyFiniteCircles
import PlanarHom.PlanarNeighborhoods

/-! The circular corner wires have disjoint entire closed traces. This is
stronger than ordinary interior disjointness and is needed for tile gluing. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph

theorem matching_curve_joint_injective {V E : Type*} {G : MultiGraph V E}
    (d : PlaneDrawing G)
    (hends : Function.Injective (fun x : E×Bool => if x.2 then G.dst x.1 else G.src x.1))
    (e f : E) (s t : I) (h : d.curve e s=d.curve f t) : e=f ∧ s=t := by
  by_cases hs0 : s=0
  · subst s
    rw [d.curve_zero] at h
    rcases (d.curve_eq_point_iff f t (G.src e)).mp h.symm with ⟨ht,hv⟩ | ⟨ht,hv⟩
    · have he := hends (show (if (f,false).2 then G.dst (f,false).1 else G.src (f,false).1)=
          (if (e,false).2 then G.dst (e,false).1 else G.src (e,false).1) from hv)
      exact ⟨(congrArg Prod.fst he).symm,ht.symm⟩
    · have he := hends (show (if (f,true).2 then G.dst (f,true).1 else G.src (f,true).1)=
          (if (e,false).2 then G.dst (e,false).1 else G.src (e,false).1) from hv)
      have hb := congrArg Prod.snd he
      contradiction
  by_cases hs1 : s=1
  · subst s
    rw [d.curve_one] at h
    rcases (d.curve_eq_point_iff f t (G.dst e)).mp h.symm with ⟨ht,hv⟩ | ⟨ht,hv⟩
    · have he := hends (show (if (f,false).2 then G.dst (f,false).1 else G.src (f,false).1)=
          (if (e,true).2 then G.dst (e,true).1 else G.src (e,true).1) from hv)
      have hb := congrArg Prod.snd he
      contradiction
    · have he := hends (show (if (f,true).2 then G.dst (f,true).1 else G.src (f,true).1)=
          (if (e,true).2 then G.dst (e,true).1 else G.src (e,true).1) from hv)
      exact ⟨(congrArg Prod.fst he).symm,ht.symm⟩
  have hs := PlaneDrawing.inside_of_ne_endpoints hs0 hs1
  by_cases ht0 : t=0
  · rw [ht0,d.curve_zero] at h
    exact (d.interior_avoids e s hs (G.src f) h).elim
  by_cases ht1 : t=1
  · rw [ht1,d.curve_one] at h
    exact (d.interior_avoids e s hs (G.dst f) h).elim
  exact d.interior_injective e f s t hs (PlaneDrawing.inside_of_ne_endpoints ht0 ht1) h

namespace CornerOrder

theorem next_injective {n : ℕ} : Function.Injective (@next n) := by
  intro a b h
  have ha := a.isLt
  have hb := b.isLt
  have hv := congrArg Fin.val h
  apply Fin.ext
  unfold next at hv
  split_ifs at hv <;> dsimp at hv <;> omega

theorem endpoint_injective (n k : ℕ) : Function.Injective
    (fun x : (Fin n×Fin k)×Bool => if x.2 then (graph n k).dst x.1 else (graph n k).src x.1) := by
  rintro ⟨⟨i,a⟩,b⟩ ⟨⟨j,c⟩,d⟩ h
  have ha := a.isLt
  have hc := c.isLt
  cases b <;> cases d
  · have hi := congrArg Prod.fst h
    have hx := congrArg (fun x : Fin n×Fin (2*k) => x.2.val) h
    change k+a.val=k+c.val at hx
    have hac : a=c := Fin.ext (by omega)
    exact Prod.ext (Prod.ext hi hac) rfl
  · have hx := congrArg (fun x : Fin n×Fin (2*k) => x.2.val) h
    change k+a.val=k-1-c.val at hx
    omega
  · have hx := congrArg (fun x : Fin n×Fin (2*k) => x.2.val) h
    change k-1-a.val=k+c.val at hx
    omega
  · have hi := next_injective (congrArg Prod.fst h)
    have hx := congrArg (fun x : Fin n×Fin (2*k) => x.2.val) h
    change k-1-a.val=k-1-c.val at hx
    have hac : a=c := Fin.ext (by omega)
    exact Prod.ext (Prod.ext hi hac) rfl

theorem placedDrawing_joint_injective (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (p : Plane) (r : ℝ) (hr : 0<r)
    (e f : Fin n×Fin k) (s t : I)
    (h : (placedDrawing n k height hanti p r hr).curve e s=
      (placedDrawing n k height hanti p r hr).curve f t) : e=f ∧ s=t :=
  matching_curve_joint_injective _ (endpoint_injective n k) e f s t h

private theorem boundary_length (h : ℝ) : rayLength (diskMap (0,h))=1 := by
  have hs := rayLength_sq (diskMap (0,h))
  have hn := rayLength_nonneg (diskMap (0,h))
  rw [diskMap_boundary] at hs
  nlinarith

theorem placedDrawing_point_circle (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (p : Plane) (r : ℝ) (hr : 0<r)
    (v : Fin n×Fin (2*k)) :
    rayLength ((placedDrawing n k height hanti p r hr).point v-p)=r := by
  rw [placedDrawing_point,add_sub_cancel_left,rayLength_smul,abs_of_pos hr,boundary_length,mul_one]

theorem placedDrawing_closed (n k : ℕ) (height : Fin (n*(2*k))→ℝ)
    (hanti : StrictAnti height) (p : Plane) (r : ℝ) (hr : 0<r)
    (e : Fin n×Fin k) (t : I) :
    rayLength ((placedDrawing n k height hanti p r hr).curve e t-p)≤r := by
  by_cases ht0 : t=0
  · rw [ht0,(placedDrawing n k height hanti p r hr).curve_zero,placedDrawing_point_circle]
  by_cases ht1 : t=1
  · rw [ht1,(placedDrawing n k height hanti p r hr).curve_one,placedDrawing_point_circle]
  exact (placedDrawing_interior n k height hanti p r hr e t
    (PlaneDrawing.inside_of_ne_endpoints ht0 ht1)).le

end CornerOrder
end PlanarHom.RadialPottsAssemblyGeometry
