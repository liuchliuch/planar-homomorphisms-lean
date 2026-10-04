import PlanarHom.RadialPottsTileIntegerDrawing
import PlanarHom.RadialPottsTileBoxBounds
import PlanarHom.PlaneDrawingMap

/-! NEW reconstruction of the missing all-k tile boundary drawing API.
The genuine integer certificate gives the original graph an explicit drawing;
all white vertices and open edges are strictly inside the terminal square. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.HardcoreLogicGadgets.IntegerDrawingCertificate
abbrev realPoint := IntegerStraightDrawing.toPlane
end PlanarHom.HardcoreLogicGadgets.IntegerDrawingCertificate
namespace PlanarHom.RadialPottsTile
open MultiGraph IntegerStraightDrawing HardcoreLogicGadgets
open HardcoreLogicGadgets.IntegerDrawingCertificate

abbrev quarterTurn := RadialPottsTileCoordinates.turn

def radius (k : ℕ) : ℝ := 10*(k+1)
def scaleMap : C(Plane,Plane) where
  toFun p := (10*p.1,10*p.2)
  continuous_toFun := by fun_prop

theorem scaleMap_injective : Function.Injective scaleMap := by
  intro p q h
  have hx:=congrArg Prod.fst h
  have hy:=congrArg Prod.snd h
  apply Prod.ext <;> dsimp [scaleMap] at hx hy <;> linarith

def drawing (k : ℕ) : PlaneDrawing (graph k) :=
  mapPlaneDrawing (RadialPottsTileGeometry.unscaledDrawing k) scaleMap scaleMap_injective

@[simp] theorem drawing_point {k : ℕ} (v : Vertex k) :
    (drawing k).point v=(10*((RadialPottsTileCoordinates.point v).1:ℝ),10*((RadialPottsTileCoordinates.point v).2:ℝ)) := rfl

theorem port_point {k : ℕ} (s : Fin 4) (a : Fin k) :
    (drawing k).point (.inr (s,a))=
      realPoint (quarterTurn s (20*(a.val:ℤ)-10*k+10,10*((k:ℤ)+1))) := by
  rw [drawing_point]
  fin_cases s <;> ext <;> simp [RadialPottsTileCoordinates.point,RadialPottsTileCoordinates.turn,
    quarterTurn,realPoint,toPlane] <;> ring

theorem point_bounds {k : ℕ} (v : Vertex k) :
    -radius k≤((drawing k).point v).1 ∧ ((drawing k).point v).1≤radius k ∧
    -radius k≤((drawing k).point v).2 ∧ ((drawing k).point v).2≤radius k := by
  have hh := RadialPottsTileCoordinates.point_box v
  have h1 : -(k:ℝ)-1≤(RadialPottsTileCoordinates.point v).1 := by exact_mod_cast hh.1
  have h2 : ((RadialPottsTileCoordinates.point v).1:ℝ)≤k+1 := by exact_mod_cast hh.2.1
  have h3 : -(k:ℝ)-1≤(RadialPottsTileCoordinates.point v).2 := by exact_mod_cast hh.2.2.1
  have h4 : ((RadialPottsTileCoordinates.point v).2:ℝ)≤k+1 := by exact_mod_cast hh.2.2.2
  rw [drawing_point]
  dsimp [radius]
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem white_point_inner {k : ℕ} (w : White k) :
    -radius k<((drawing k).point (.inl w)).1 ∧ ((drawing k).point (.inl w)).1<radius k ∧
    -radius k<((drawing k).point (.inl w)).2 ∧ ((drawing k).point (.inl w)).2<radius k := by
  have hh := RadialPottsTileCoordinates.white_box w
  have h1 : -(k:ℝ)-1<(RadialPottsTileCoordinates.point (.inl w)).1 := by exact_mod_cast hh.1
  have h2 : ((RadialPottsTileCoordinates.point (.inl w)).1:ℝ)<k+1 := by exact_mod_cast hh.2.1
  have h3 : -(k:ℝ)-1<(RadialPottsTileCoordinates.point (.inl w)).2 := by exact_mod_cast hh.2.2.1
  have h4 : ((RadialPottsTileCoordinates.point (.inl w)).2:ℝ)<k+1 := by exact_mod_cast hh.2.2.2
  rw [drawing_point]
  dsimp [radius]
  constructor; linarith
  constructor; linarith
  constructor <;> linarith

theorem drawing_curve {k : ℕ} (e : Edge k) (t : I) :
    (drawing k).curve e t=affine ((drawing k).point ((graph k).src e))
      ((drawing k).point ((graph k).dst e)) t := by
  ext <;> dsimp [drawing,mapPlaneDrawing,RadialPottsTileGeometry.unscaledDrawing,
    IntegerStraightDrawing.drawing,IntegerStraightDrawing.curve,scaleMap,affine] <;> ring

theorem curve_interior_inside {k : ℕ} (e : Edge k) (t : I) (ht : Inside t) :
    -radius k<((drawing k).curve e t).1 ∧ ((drawing k).curve e t).1<radius k ∧
    -radius k<((drawing k).curve e t).2 ∧ ((drawing k).curve e t).2<radius k := by
  have hs : ∃w,(graph k).src e=.inl w := by
    cases e with
    | inl e => exact ⟨_,rfl⟩
    | inr e => exact ⟨_,rfl⟩
  obtain ⟨w,hw⟩:=hs
  have hsource:=white_point_inner w
  have htarget:=point_bounds ((graph k).dst e)
  rw [drawing_curve,hw]
  dsimp [affine]
  have ht0:=ht.1
  have ht1:=ht.2
  have blend (x y R : ℝ) (hx : -R<x ∧ x<R) (hy : -R≤y ∧ y≤R) :
      -R<(1-(t:ℝ))*x+(t:ℝ)*y ∧ (1-(t:ℝ))*x+(t:ℝ)*y<R := by
    constructor
    · nlinarith [mul_pos (show 0<1-(t:ℝ) by linarith) (show 0<x+R by linarith),
        mul_nonneg ht0.le (show 0≤y+R by linarith)]
    · nlinarith [mul_pos (show 0<1-(t:ℝ) by linarith) (show 0<R-x by linarith),
        mul_nonneg ht0.le (show 0≤R-y by linarith)]
  have hx:=blend _ _ _ ⟨hsource.1,hsource.2.1⟩ ⟨htarget.1,htarget.2.1⟩
  have hy:=blend _ _ _ ⟨hsource.2.2.1,hsource.2.2.2⟩ ⟨htarget.2.2.1,htarget.2.2.2⟩
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

end PlanarHom.RadialPottsTile
