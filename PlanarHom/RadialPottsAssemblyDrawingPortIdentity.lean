import PlanarHom.RadialPottsAssemblyDegrees
import PlanarHom.RadialPottsAssemblyPortLevels
import PlanarHom.RadialPottsAssemblyRibbonCircleClip

/-! Exact subtype-valued terminal coordinates and actual clipped-band port
positions. The identities retain both endpoint darts of a loop. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph RadialPottsTile RadialPottsAssemblyGeometry

/-- The subtype-valued square coordinate, without forgetting either bound. -/
theorem squarePoint_sideOfBits {k : ℕ} (b c : Bool) (a : Fin k) :
    squarePoint (.inr (sideOfBits b c,a)) =
      ((if b then 0 else 1),orientedLevel portLevel b (portIndex (sideOfBits b c) a)) := by
  have h := square_port_level (sideOfBits b c) a
  cases b <;> cases c <;> apply Prod.ext <;> apply Subtype.ext
  all_goals
    first
    | simpa only [sideOfBits,Fin.reduceFinMk,Fin.isValue,Fin.val_zero,Fin.val_one,
        Fin.val_ofNat,decide_true,decide_false,↓reduceIte] using congrArg Prod.fst h
    | simpa only [sideOfBits,Fin.reduceFinMk,Fin.isValue,Fin.val_zero,Fin.val_one,
        Fin.val_ofNat,decide_true,decide_false,↓reduceIte] using congrArg Prod.snd h

/-- Odd ports use the second half of the finite circular row. -/
theorem portIndex_odd {k : ℕ} (b : Bool) (a : Fin k) :
    portIndex (sideOfBits b true) a=⟨k+a.val,by omega⟩ := by
  cases b <;> rfl

/-- Reversed even ports use the reversed first half of the next row. -/
theorem portIndex_even_reverse {k : ℕ} (b : Bool) (a : Fin k) :
    portIndex (sideOfBits b false) (reverseLane a)=
      ⟨k-1-a.val,by have := a.isLt; omega⟩ := by
  cases b <;> rfl

end PlanarHom.RadialPotts.Assembly

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry RadialPotts.Assembly
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)} {τ : C(I,I)}

/-- A literal tile port lies exactly on its outgoing dart's selected fan ray. -/
theorem band_squarePoint_sideOfBits (C : CircleClipping F τ) (hτ : Function.Injective τ)
    (e : E) (b c : Bool) {k : ℕ} (a : Fin k) :
    C.band hτ e (squarePoint (.inr (sideOfBits b c,a))) =
      d.drawing.point (G.dartPair (e,b)).1+C.radius •
        circleRay ((F (e,b)).direction
          (τ (orientedLevel portLevel b (portIndex (sideOfBits b c) a)) : ℝ)) := by
  rw [squarePoint_sideOfBits]
  cases b
  · exact C.band_one hτ e _
  · exact C.band_zero hτ e _

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
