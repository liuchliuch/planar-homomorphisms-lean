import PlanarHom.RadialPottsAssemblyDrawingTails

/-! Literal geometric gluing: extend only the existing outer long occurrence
to the midpoint of its corner wire. No connector edge is added or contracted. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsAssemblyGeometry
variable {E : Type} {k : ℕ}
namespace DrawingData
variable {rotation : Equiv.Perm (Medial.Dart E)} (B : DrawingData rotation k)

def extensionPath (e : E) (f : Edge k) (p : Port k)
    (hf : (RadialPottsTile.graph k).dst f=.inr p) :
    Path (B.tilePoint e ((RadialPottsTile.graph k).dst f))
      (B.point (.inr (portImage rotation e p))) where
  toContinuousMap := B.tail e p
  source' := (B.tail_zero e p).trans (congrArg (B.tilePoint e) hf).symm
  target' := B.tail_one e p

def extendedPath (e : E) (f : Edge k) (p : Port k)
    (hf : (RadialPottsTile.graph k).dst f=.inr p) :
    Path (B.tilePoint e ((RadialPottsTile.graph k).src f))
      (B.point (.inr (portImage rotation e p))) :=
  (B.tilePath e f).trans (B.extensionPath e f p hf)

theorem extendedPath_injective (e : E) (f : Edge k) (p : Port k)
    (hf : (RadialPottsTile.graph k).dst f=.inr p) :
    Function.Injective (B.extendedPath e f p hf) := by
  apply Polygonal.path_trans_injective
  · exact B.tilePath_port_injective e f p hf
  · exact B.tail_injective e p
  · rintro z ⟨s,hs⟩ ⟨t,ht⟩
    by_cases ht0 : t=0
    · subst t
      exact ht.symm.trans (B.extensionPath e f p hf).source
    · have htpos : (0:I)<t := lt_of_le_of_ne (bot_le) (Ne.symm ht0)
      exact (B.band_ne_tail htpos (hs.trans ht.symm)).elim

/-- Internal occurrences retain the old curve; only an occurrence whose actual
destination is a port receives that port's half-wire. -/
def curve (e : E) (f : Edge k) : C(I,Plane) :=
  if h : ∃ p, (RadialPottsTile.graph k).dst f=.inr p then
    (B.extendedPath e f h.choose h.choose_spec).toContinuousMap
  else B.tileCurve e f

theorem curve_of_port (e : E) (f : Edge k) (p : Port k)
    (hf : (RadialPottsTile.graph k).dst f=.inr p) :
    B.curve e f=(B.extendedPath e f p hf).toContinuousMap := by
  have h : ∃ q, (RadialPottsTile.graph k).dst f=.inr q := ⟨p,hf⟩
  have hp : h.choose=p := Sum.inr.inj (h.choose_spec.symm.trans hf)
  simp only [curve,dif_pos h]
  subst p
  rfl

theorem curve_of_white (e : E) (f : Edge k) (w : White k)
    (hf : (RadialPottsTile.graph k).dst f=.inl w) : B.curve e f=B.tileCurve e f := by
  apply dif_neg
  rintro ⟨p,hp⟩
  rw [hf] at hp
  exact Sum.inl_ne_inr hp

theorem point_embed_src (e : E) (f : Edge k) :
    B.point (embed rotation e ((RadialPottsTile.graph k).src f))=
      B.tilePoint e ((RadialPottsTile.graph k).src f) := by
  obtain ⟨w,hw⟩ := tile_src_white f
  rw [hw]
  rfl

@[simp] theorem curve_zero (e : E) (f : Edge k) :
    B.curve e f 0=B.point (embed rotation e ((RadialPottsTile.graph k).src f)) := by
  rw [B.point_embed_src]
  unfold curve
  split_ifs
  · exact (B.extendedPath _ _ _ _).source
  · exact B.tileCurve_zero e f

@[simp] theorem curve_one (e : E) (f : Edge k) :
    B.curve e f 1=B.point (embed rotation e ((RadialPottsTile.graph k).dst f)) := by
  cases hf : (RadialPottsTile.graph k).dst f with
  | inl w => rw [B.curve_of_white e f w hf,B.tileCurve_one,hf]; rfl
  | inr p => rw [B.curve_of_port e f p hf]; exact (B.extendedPath e f p hf).target

/-- The only possible interior pieces are an old open tile curve, its unique
terminal junction, or the open part of its assigned half-wire. -/
def InteriorPiece (e : E) (f : Edge k) (z : Plane) : Prop :=
  (∃ s, Inside s ∧ z=B.tileCurve e f s) ∨
  (∃ p, (RadialPottsTile.graph k).dst f=.inr p ∧ z=B.tilePoint e (.inr p)) ∨
  (∃ p t, (RadialPottsTile.graph k).dst f=.inr p ∧ 0<t ∧ t<1 ∧ z=B.tail e p t)

theorem curve_interior_piece (e : E) (f : Edge k) (t : I) (ht : Inside t) :
    B.InteriorPiece e f (B.curve e f t) := by
  by_cases hf : ∃ p, (RadialPottsTile.graph k).dst f=.inr p
  · obtain ⟨p,hp⟩ := hf
    rw [B.curve_of_port e f p hp]
    let P := B.extendedPath e f p hp
    have hinj := B.extendedPath_injective e f p hp
    have hr : P t ∈ Set.range (B.tilePath e f) ∪ Set.range (B.extensionPath e f p hp) := by
      rw [← Path.trans_range]
      exact ⟨t,rfl⟩
    rcases hr with ⟨s,hs⟩ | ⟨s,hs⟩
    · by_cases hs0 : s=0
      · subst s
        have h0 : t=0 := hinj (hs.symm.trans ((B.tilePath e f).source.trans P.source.symm))
        exact (ne_of_gt (show (0:I)<t from ht.1) h0).elim
      by_cases hs1 : s=1
      · subst s
        right; left
        exact ⟨p,hp,hs.symm.trans ((B.tilePath e f).target.trans (congrArg (B.tilePoint e) hp))⟩
      left
      exact ⟨s,PlaneDrawing.inside_of_ne_endpoints hs0 hs1,hs.symm⟩
    · by_cases hs0 : s=0
      · subst s
        right; left
        exact ⟨p,hp,hs.symm.trans ((B.extensionPath e f p hp).source.trans (congrArg (B.tilePoint e) hp))⟩
      by_cases hs1 : s=1
      · subst s
        have h1 : t=1 := hinj (hs.symm.trans ((B.extensionPath e f p hp).target.trans P.target.symm))
        exact (ne_of_lt (show t<(1:I) from ht.2) h1).elim
      right; right
      have hsi := PlaneDrawing.inside_of_ne_endpoints hs0 hs1
      exact ⟨p,s,hp,hsi.1,hsi.2,hs.symm⟩
  · change B.InteriorPiece e f ((if h : ∃ p, (RadialPottsTile.graph k).dst f=.inr p then
        (B.extendedPath e f h.choose h.choose_spec).toContinuousMap else B.tileCurve e f) t)
    rw [dif_neg hf]
    exact Or.inl ⟨t,ht,rfl⟩

theorem curve_self_interior_injective (e : E) (f : Edge k) {s t : I}
    (hs : Inside s) (ht : Inside t) (h : B.curve e f s=B.curve e f t) : s=t := by
  by_cases hf : ∃ p, (RadialPottsTile.graph k).dst f=.inr p
  · obtain ⟨p,hp⟩ := hf
    rw [B.curve_of_port e f p hp] at h
    exact B.extendedPath_injective e f p hp h
  · simp only [curve,dif_neg hf] at h
    exact (B.tileCurve_interior_injective hs ht h).2.2

theorem interiorPiece_avoids {e : E} {f : Edge k} {z : Plane}
    (hz : B.InteriorPiece e f z) (v : Vertex E k) : z≠B.point v := by
  rcases hz with ⟨s,hs,rfl⟩ | ⟨p,hp,rfl⟩ | ⟨p,t,hp,ht0,ht1,rfl⟩
  · cases v with
    | inl v => exact B.tileCurve_interior_avoids hs _
    | inr v => exact B.band_ne_wire _ _ _ _ PlaneDrawing.half_inside
  · cases v with
    | inl v =>
      intro h
      exact Sum.inr_ne_inl (B.tilePoint_joint_injective h).2
    | inr v => exact B.band_ne_wire _ _ _ _ PlaneDrawing.half_inside
  · exact B.tail_ne_point ht0 ht1 v

theorem interiorPiece_owner {e f : E} {a b : Edge k} {z : Plane}
    (ha : B.InteriorPiece e a z) (hb : B.InteriorPiece f b z) : e=f ∧ a=b := by
  rcases ha with ⟨s,hs,hz⟩ | ⟨p,hp,hz⟩ | ⟨p,s,hp,hs0,hs1,hz⟩
  · rcases hb with ⟨t,ht,hz'⟩ | ⟨q,hq,hz'⟩ | ⟨q,t,hq,ht0,ht1,hz'⟩
    · have h := B.tileCurve_interior_injective hs ht (hz.symm.trans hz')
      exact ⟨h.1,h.2.1⟩
    · exact (B.tileCurve_interior_avoids hs _ (hz.symm.trans hz')).elim
    · exact (B.band_ne_tail ht0 (hz.symm.trans hz')).elim
  · rcases hb with ⟨t,ht,hz'⟩ | ⟨q,hq,hz'⟩ | ⟨q,t,hq,ht0,ht1,hz'⟩
    · exact (B.tileCurve_interior_avoids ht _ (hz'.symm.trans hz)).elim
    · obtain ⟨hef,hpq⟩ := B.tilePoint_joint_injective (hz.symm.trans hz')
      have hpq' := Sum.inr.inj hpq
      subst q
      exact ⟨hef,tile_dst_port_unique hp hq⟩
    · exact (B.band_ne_tail ht0 (hz.symm.trans hz')).elim
  · rcases hb with ⟨t,ht,hz'⟩ | ⟨q,hq,hz'⟩ | ⟨q,t,hq,ht0,ht1,hz'⟩
    · exact (B.band_ne_tail hs0 (hz'.symm.trans hz)).elim
    · exact (B.band_ne_tail hs0 (hz'.symm.trans hz)).elim
    · obtain ⟨hef,hpq,hst⟩ := B.tail_joint_injective hs1 ht1 (hz.symm.trans hz')
      subst q
      exact ⟨hef,tile_dst_port_unique hp hq⟩

/-- Actual crossing-free assembly on the exact original occurrence type.
Loops and parallel original occurrences need no separate case or simplification. -/
def drawing : PlaneDrawing (graph rotation k) where
  point := B.point
  point_injective := B.point_injective
  curve x := B.curve x.1 x.2
  curve_zero x := B.curve_zero x.1 x.2
  curve_one x := B.curve_one x.1 x.2
  interior_injective := by
    rintro ⟨e,a⟩ ⟨f,b⟩ s t hs ht h
    obtain ⟨hef,hab⟩ := B.interiorPiece_owner (B.curve_interior_piece e a s hs)
      (h ▸ B.curve_interior_piece f b t ht)
    subst f; subst b
    exact ⟨rfl,B.curve_self_interior_injective e a hs ht h⟩
  interior_avoids := by
    rintro ⟨e,f⟩ t ht v
    exact B.interiorPiece_avoids (B.curve_interior_piece e f t ht) v

include B in
theorem planar : (graph rotation k).Planar := ⟨drawing B⟩

end DrawingData
end PlanarHom.RadialPotts.Assembly
