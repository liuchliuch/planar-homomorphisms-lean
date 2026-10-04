import PlanarHom.RadialPottsAssemblyDrawingData

/-! The two actual half-wires attached to each port fiber. They share exactly
their midpoint and remain distinct even if both ends belong to one loop tile. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsAssemblyGeometry
variable {E : Type} {k : ℕ}
namespace DrawingData
variable {rotation : Equiv.Perm (Medial.Dart E)} (B : DrawingData rotation k)

def tailParameter (b : Bool) : C(I,I) where
  toFun t := if b then ⟨(t:ℝ)/2,by constructor <;> linarith [t.2.1,t.2.2]⟩
    else ⟨1-(t:ℝ)/2,by constructor <;> linarith [t.2.1,t.2.2]⟩
  continuous_toFun := by cases b <;> simp only [Bool.false_eq_true,↓reduceIte] <;> fun_prop

@[simp] theorem tailParameter_zero (b : Bool) : tailParameter b 0=(if b then 0 else 1) := by
  cases b <;> apply Subtype.ext <;> norm_num [tailParameter]
@[simp] theorem tailParameter_one (b : Bool) : tailParameter b 1=PlaneDrawing.half := by
  cases b <;> apply Subtype.ext <;> norm_num [tailParameter,PlaneDrawing.half]

theorem tailParameter_inside (b : Bool) {t : I} (ht : 0<t) : Inside (tailParameter b t) := by
  have ht' : (0:ℝ)<t := ht
  cases b <;> dsimp [Inside,tailParameter] <;> constructor <;> linarith [t.2.2]

theorem tailParameter_ne_half (b : Bool) {t : I} (ht : t<1) :
    tailParameter b t ≠ PlaneDrawing.half := by
  intro h
  have hh := congrArg (fun x : I => (x:ℝ)) h
  have ht' : (t:ℝ)<1 := ht
  cases b <;> dsimp [tailParameter,PlaneDrawing.half] at hh <;> linarith

theorem tailParameter_injective (b : Bool) : Function.Injective (tailParameter b) := by
  intro s t h
  have hh := congrArg (fun x : I => (x:ℝ)) h
  apply Subtype.ext
  cases b <;> dsimp [tailParameter] at hh <;> linarith

theorem tailParameter_joint_injective {b c : Bool} {s t : I} (hs : s<1) (ht : t<1)
    (h : tailParameter b s=tailParameter c t) : b=c ∧ s=t := by
  have hh := congrArg (fun x : I => (x:ℝ)) h
  have hs' : (s:ℝ)<1 := hs
  have ht' : (t:ℝ)<1 := ht
  cases b <;> cases c
  · exact ⟨rfl,tailParameter_injective false h⟩
  · dsimp [tailParameter] at hh; exfalso; linarith
  · dsimp [tailParameter] at hh; exfalso; linarith
  · exact ⟨rfl,tailParameter_injective true h⟩

def tail (e : E) (p : Port k) : C(I,Plane) :=
  (B.wire (portFiberEquiv rotation (e,p)).1).comp
    (tailParameter (portFiberEquiv rotation (e,p)).2)

@[simp] theorem tail_zero (e : E) (p : Port k) :
    B.tail e p 0=B.tilePoint e (.inr p) := by
  have h := (portFiberEquiv rotation).symm_apply_apply (e,p)
  change portPreimage rotation (portFiberEquiv rotation (e,p)).1
    (portFiberEquiv rotation (e,p)).2=(e,p) at h
  dsimp [tail]
  rw [tailParameter_zero]
  cases hb : (portFiberEquiv rotation (e,p)).2
  · simp only [Bool.false_eq_true,↓reduceIte]
    rw [B.wire_one]
    rw [hb] at h
    simpa [h,tilePoint]
  · simp only [↓reduceIte]
    rw [B.wire_zero]
    rw [hb] at h
    simpa [h,tilePoint]

@[simp] theorem tail_one (e : E) (p : Port k) :
    B.tail e p 1=B.point (.inr (portImage rotation e p)) := by
  simp [tail,point,portFiberEquiv]

theorem tail_injective (e : E) (p : Port k) : Function.Injective (B.tail e p) := by
  intro s t h
  exact tailParameter_injective _ (B.wire_joint_injective _ _ _ _ h).2

theorem tail_joint_injective {e f : E} {p q : Port k} {s t : I}
    (hs : s<1) (ht : t<1) (h : B.tail e p s=B.tail f q t) : e=f ∧ p=q ∧ s=t := by
  obtain ⟨hw,hp⟩ := B.wire_joint_injective _ _ _ _ h
  obtain ⟨hb,hst⟩ := tailParameter_joint_injective hs ht hp
  have he := (portFiberEquiv rotation).injective (Prod.ext hw hb)
  exact ⟨congrArg Prod.fst he,congrArg Prod.snd he,hst⟩

theorem band_ne_tail {e f : E} {p : I×I} {q : Port k} {t : I} (ht : 0<t) :
    B.band e p ≠ B.tail f q t :=
  B.band_ne_wire _ _ _ _ (tailParameter_inside _ ht)

theorem tail_ne_point {e : E} {p : Port k} {t : I} (ht : 0<t) (ht1 : t<1)
    (v : Vertex E k) : B.tail e p t ≠ B.point v := by
  intro h
  cases v with
  | inl v => exact B.band_ne_tail ht h.symm
  | inr v =>
    exact tailParameter_ne_half _ ht1 (B.wire_joint_injective _ _ _ _ h).2

/-- The old tile path, before appending a half of a real corner curve. -/
def tilePath (e : E) (f : Edge k) :
    Path (B.tilePoint e ((RadialPottsTile.graph k).src f))
      (B.tilePoint e ((RadialPottsTile.graph k).dst f)) where
  toContinuousMap := B.tileCurve e f
  source' := B.tileCurve_zero e f
  target' := B.tileCurve_one e f

theorem tilePath_port_injective (e : E) (f : Edge k) (p : Port k)
    (hf : (RadialPottsTile.graph k).dst f=.inr p) : Function.Injective (B.tilePath e f) := by
  have hne : (RadialPottsTile.graph k).src f≠(RadialPottsTile.graph k).dst f := by
    obtain ⟨w,hw⟩ := tile_src_white f
    rw [hw,hf]
    exact Sum.inl_ne_inr
  intro s t h
  have hp := (B.band_joint_injective e e _ _ h).2
  exact (squareDrawing k).edgePath_injective f hne
    (congrArg (fun p : I×I => ((p.1:ℝ),(p.2:ℝ))) hp)

end DrawingData
end PlanarHom.RadialPotts.Assembly
