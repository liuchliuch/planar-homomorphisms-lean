import PlanarHom.RadialPottsAssemblyRibbonGerms

/-! Parallel copies are literal constant-height slices of the source's actual
polygonal ribbons. Their finite polygonal chains and endpoint germs are proved
for these same curves, so no unrelated planar redrawing changes the rotation. -/
noncomputable section
open Classical Set unitInterval
namespace PlanarHom.Polygonal.Chain
open MultiGraph
variable {U : Set Plane} {x y x' y' : Plane}

 def castEndpoints (p : Chain U x y) (hx : x=x') (hy : y=y') : Chain U x' y' := hx ▸ hy ▸ p
 theorem castEndpoints_path (p : Chain U x y) (hx : x=x') (hy : y=y') (t : I) :
    (p.castEndpoints hx hy).strictPath t=p.strictPath t := by subst x'; subst y'; rfl
end PlanarHom.Polygonal.Chain

namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
open Polygonal Kasteleyn PlanarityLRRealization
variable {V E : Type} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G}

 def parallelDrawing (D : d.TwoSidedStripData) (positive : Bool) {t : ℕ}
    (level : Fin t→I) (hinj : Function.Injective level) : PlaneDrawing (G.thicken t) where
  point := d.drawing.point
  point_injective := d.drawing.point_injective
  curve e := ((D.sideRibbon positive).band e.1).comp (RibbonDrawing.slice (level e.2))
  curve_zero e := (D.sideRibbon positive).band_zero e.1 (level e.2)
  curve_one e := (D.sideRibbon positive).band_one e.1 (level e.2)
  interior_injective := by
    rintro ⟨e,i⟩ ⟨f,j⟩ s u hs hu he
    obtain ⟨hef,hcoord⟩ := (D.sideRibbon positive).band_injective e f (s,level i) (u,level j) hs hu he
    exact ⟨Prod.ext hef (hinj (congrArg Prod.snd hcoord)),congrArg Prod.fst hcoord⟩
  interior_avoids e s hs v := (D.sideRibbon positive).band_avoids e.1 (s,level e.2) hs v

 def sliceVertex (D : d.TwoSidedStripData) (positive : Bool) (s : I) (v : Plane) : Plane :=
  v+(s:ℝ) • ((v+D.width • D.signedNormal positive v)-v)

 theorem sliceVertex_host (D : d.TwoSidedStripData) (positive : Bool) (s : I) (v : V) :
    D.sliceVertex positive s (d.drawing.point v)=d.drawing.point v := by
  simp [sliceVertex,D.signedNormal_host positive _ ⟨v,rfl⟩]

 def parallelChain (D : d.TwoSidedStripData) (positive : Bool) {t : ℕ}
    (level : Fin t→I) (e : E×Fin t) :
    Chain Set.univ (d.drawing.point ((G.thicken t).src e)) (d.drawing.point ((G.thicken t).dst e)) :=
  ((d.chain e.1).mapVertices (D.sliceVertex positive (level e.2))).castEndpoints
    (D.sliceVertex_host positive (level e.2) (G.src e.1))
    (D.sliceVertex_host positive (level e.2) (G.dst e.1))

 theorem parallelChain_path (D : d.TwoSidedStripData) (positive : Bool) {t : ℕ}
    (level : Fin t→I) (e : E×Fin t) (u : I) :
    (D.parallelChain positive level e).strictPath u=
      (D.sideRibbon positive).band e.1 (u,level e.2) := by
  rw [parallelChain,Chain.castEndpoints_path]
  change ((d.chain e.1).mapVertices
    (fun v => v+(level e.2:ℝ) • ((v+D.width • D.signedNormal positive v)-v))).strictPath u=_
  rw [Chain.strictPath_mapVertices_affine]
  rfl

 def parallelPolygonalDrawing (D : d.TwoSidedStripData) (positive : Bool) {t : ℕ}
    (level : Fin t→I) (hinj : Function.Injective level) : PolygonalDrawing (G.thicken t) where
  drawing := D.parallelDrawing positive level hinj
  chain := D.parallelChain positive level
  curve_eq e := by
    apply ContinuousMap.ext
    intro u
    exact (D.parallelChain_path positive level e u).symm

 theorem parallel_straightGerm (D : d.TwoSidedStripData) (positive : Bool) {t : ℕ}
    (level : Fin t→I) (hinj : Function.Injective level) (rays : Dart E→Plane)
    (F : ∀a,D.EndpointFan positive a (rays a)) (e : E×Fin t) (b : Bool) :
    StraightGerm ((D.parallelPolygonalDrawing positive level hinj).drawing.dartPath (e,b))
      ((D.parallelPolygonalDrawing positive level hinj).drawing.point ((G.thicken t).dartPair (e,b)).1)
      ((F (e.1,b)).direction (level e.2:ℝ)) := by
  have h := (F (e.1,b)).straightGerm (level e.2)
  cases b <;> exact h
end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData
