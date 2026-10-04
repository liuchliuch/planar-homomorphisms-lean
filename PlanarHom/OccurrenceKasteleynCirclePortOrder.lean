import PlanarHom.PlanarityCircleCrossing
import PlanarHom.RadialPottsAssemblyRibbonCircleClip

/-! NEW circular order forced by the actual recovered circle-clipped bands.
No noninterleaving order is supplied as a hypothesis. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn Polygonal RadialPottsAssemblyGeometry PlanarityCircleCrossing
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)} {τ : C(I,I)}

/-- Two literal clipped occurrence slices cannot join alternating circle ports
around the same original host. Band separation and exterior clearance are taken
from the unchanged recovered CircleClipping consumer. -/
theorem no_alternating_circle_ports (C : CircleClipping F τ) (hτ : Function.Injective τ)
    {e f : E} (hef : e≠f) (s t : I) (v : V) {a b c k : ℝ}
    (hab : a<b) (hbc : b<c) (hck : c<k)
    (ha : C.band hτ e (0,s)=d.drawing.point v+C.radius • diskMap (0,a))
    (hc : C.band hτ e (1,s)=d.drawing.point v+C.radius • diskMap (0,c))
    (hb : C.band hτ f (0,t)=d.drawing.point v+C.radius • diskMap (0,b))
    (hk : C.band hτ f (1,t)=d.drawing.point v+C.radius • diskMap (0,k)) : False := by
  let α : C(I,Plane) := ⟨fun u => C.band hτ e (u,s),
    (C.band hτ e).continuous.comp (continuous_id.prodMk continuous_const)⟩
  let β : C(I,Plane) := ⟨fun u => C.band hτ f (u,t),
    (C.band hτ f).continuous.comp (continuous_id.prodMk continuous_const)⟩
  obtain ⟨u,w,h⟩ := alternating_scaledCircle_paths_intersect α β (d.drawing.point v)
    C.radius C.radius_pos hab hbc hck ha hc hb hk
    (fun u hu => C.band_outside hτ e (u,s) hu v)
    (fun u hu => C.band_outside hτ f (u,t) hu v)
  exact Set.disjoint_left.mp (C.bands_disjoint hτ hef) ⟨(u,s),rfl⟩ ⟨(w,t),h.symm⟩

/-- The concrete loop-port height order used by a cut-circle representation is
constrained by ordinary planarity. Each endpoint formula is derived from the
actual endpoint fan and inverse Cayley coordinate, rather than an order oracle. -/
theorem no_alternating_loop_port_heights (C : CircleClipping F τ) (hτ : Function.Injective τ)
    {e f : E} (hef : e≠f) (s t : I) (v : V)
    (hes : G.src e=v) (het : G.dst e=v) (hfs : G.src f=v) (hft : G.dst f=v)
    (he0 : ((F (e,true)).direction (τ s : ℝ)).1≠0)
    (he1 : ((F (e,false)).direction (τ s : ℝ)).1≠0)
    (hf0 : ((F (f,true)).direction (τ t : ℝ)).1≠0)
    (hf1 : ((F (f,false)).direction (τ t : ℝ)).1≠0)
    (hab : circleHeight ((F (e,true)).direction (τ s : ℝ))<
      circleHeight ((F (f,true)).direction (τ t : ℝ)))
    (hbc : circleHeight ((F (f,true)).direction (τ t : ℝ))<
      circleHeight ((F (e,false)).direction (τ s : ℝ)))
    (hck : circleHeight ((F (e,false)).direction (τ s : ℝ))<
      circleHeight ((F (f,false)).direction (τ t : ℝ))) : False := by
  apply C.no_alternating_circle_ports hτ hef s t v hab hbc hck
  · rw [C.band_zero,hes,← diskMap_circleHeight he0]
  · rw [C.band_one,het,← diskMap_circleHeight he1]
  · rw [C.band_zero,hfs,← diskMap_circleHeight hf0]
  · rw [C.band_one,hft,← diskMap_circleHeight hf1]

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
