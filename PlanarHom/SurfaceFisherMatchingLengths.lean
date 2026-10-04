import PlanarHom.SurfaceFisherMatchingMask

/-! NEW exact serialized support length for representative and reference masks. -/
namespace PlanarHom.SurfaceFisherMatching
open Complexity SurfaceBooleanRows

theorem mask_length (g : MixedCode) (bits : Row) :
    (mask g bits).length=(FisherCubicCode.code g).edges.length := by
  simp [mask,FisherCubicCode.code,FisherCubicCode.externalEdges,FisherCubicCode.internalEdges,List.length_flatMap]

end PlanarHom.SurfaceFisherMatching
