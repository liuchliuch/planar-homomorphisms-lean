import PlanarHom.OccurrenceKasteleynTreePortWords

/-! NEW uniqueness of the literal recursive word retained by geometric routing. -/
noncomputable section
namespace PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
open Kasteleyn HostFanChart PlanarityLRRealization RootedOccurrenceTree
variable {V E : Type*} [Fintype V] [Fintype E] {G : MultiGraph V E}
variable {d : PolygonalDrawing G} {D : d.TwoSidedStripData} {positive : Bool}
variable {rays : Dart E → Plane} {F : ∀ a, D.EndpointFan positive a (rays a)}
variable {charts : ∀ v, HostFanChart F v}

theorem BranchWord.unique {tree : RootedOccurrenceTree V E} {parent : E}
    {word : List (Dart E)} (h : BranchWord charts tree parent word)
    {word' : List (Dart E)} (h' : BranchWord charts tree parent word') : word=word' := by
  induction h generalizing word' with
  | node v children words parent hdst hchildren ih =>
      cases h' with
      | node _ _ words' _ _ hchildren' =>
          have heq : words=words' := by
            funext c hc
            exact ih c hc (hchildren' c hc)
          cases heq
          rfl

theorem RootWord.unique {tree : RootedOccurrenceTree V E} {word word' : List (Dart E)}
    (h : RootWord charts tree word) (h' : RootWord charts tree word') : word=word' := by
  cases h with
  | node v children words hchildren =>
      cases h' with
      | node _ _ words' hchildren' =>
          have heq : words=words' := by
            funext c hc
            exact (hchildren c hc).unique (hchildren' c hc)
          cases heq
          rfl

end PlanarHom.MultiGraph.PolygonalDrawing.TwoSidedStripData.CircleClipping
