import PlanarHom.ColoringFramedPrivateRestriction
import PlanarHom.ColoringFramedTypedLocalRetention
import PlanarHom.ColoringFramedDartPartition

/-! Closing the source row restriction using the proved fixed framed-macro
adapters. The exact recursive marker deletion recovers the original compiler's
literal geometric rotation, with no additional row or geometry premise. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn ParsimoniousNorOneInThree FinitePermutationCycles

theorem port_retention : PortRetention := FramedMacro.cutRow_filter_port

theorem private_retention : PrivateRetention := FramedMacro.cutRow_filter_private_formPerm

theorem source_row_rotation (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    (((fullRows f).row (.inl ((Canvas.graph f).dartPair a).1)).filterMap (keepDart f)).formPerm a=
      (Canvas.geometricRows f).rotation a := retained_row_rotation port_retention private_retention f a

/-- The precise rotation equality needed to remove all proof-only seed/frame
edges and then the empty corner rows from the full framed Euler equation. -/
theorem erase_fullRows_rotation (f : NumericFormula) :
    eraseFinMarkers ((dartPartition f).permCongr (fullRows f).rotation)=(Canvas.geometricRows f).rotation := by
  apply PlanarityLRRealization.RotationRows.eraseFinMarkers_eq_of_retained_rows
  intro a
  rw [partition_symm_inl,oldDart_host,List.filterMap_map]
  have he : HostRowSystem.keepLeft ∘ dartPartition f=keepDart f := funext (partition_keep f)
  rw [he]
  exact source_row_rotation f a

end PlanarHom.ColoringEmitter.FramedCanvas
