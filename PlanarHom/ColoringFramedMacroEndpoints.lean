import PlanarHom.ColoringMacroWireFramedRetention
import PlanarHom.ColoringMacroCrossFramedRetention
import PlanarHom.ColoringMacroFanFramedRetention
import PlanarHom.ColoringMacroTestFramedRetention
import PlanarHom.ColoringFramedCanvasGraph
import PlanarHom.ColoringEmitterMacroSemantics

noncomputable section
namespace PlanarHom.ColoringEmitter.FramedMacro
open MultiGraph PositiveBlockProgram RadialPotts.Assembly
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem old_source (s : CellShape) (e : LocalPatch.Edge s) :
    (graph s).src (oldEdge s e)=oldVertex s ((LocalPatch.numericGraph s).src e) := by
  cases s
  case wireTop =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireTop e,false)).val)=
      (LocalPatch.edgePair .wireTop e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.WireFramed.retained_source (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case wireBottom =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireBottom e,false)).val)=
      (LocalPatch.edgePair .wireBottom e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.WireFramed.retained_source (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case wireDown =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireDown e,false)).val)=
      (LocalPatch.edgePair .wireDown e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.WireFramed.retained_source (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case cross =>
    apply Fin.ext
    change ColoringMacroFaces.CrossFramed.hostValue ((dartIndexEquiv 3168 (oldEdge .cross e,false)).val)=
      (LocalPatch.edgePair .cross e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.CrossFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.CrossFramed.retained_source (ColoringCrossMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringCrossMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringCrossMacroEmitterJoin.edgePair_eq e)).symm
  case fan =>
    apply Fin.ext
    change ColoringMacroFaces.FanFramed.hostValue ((dartIndexEquiv 2632 (oldEdge .fan e,false)).val)=
      (LocalPatch.edgePair .fan e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.FanFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.FanFramed.retained_source (ColoringFanMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringFanMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringFanMacroEmitterJoin.edgePair_eq e)).symm
  case test =>
    apply Fin.ext
    change ColoringMacroFaces.TestFramed.hostValue ((dartIndexEquiv 285 (oldEdge .test e,false)).val)=
      (LocalPatch.edgePair .test e).1
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.TestFramed.hostValue (2*e.val)=_
    have h:=ColoringMacroFaces.TestFramed.retained_source (ColoringTestMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringTestMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.fst (ColoringTestMacroEmitterJoin.edgePair_eq e)).symm
theorem old_target (s : CellShape) (e : LocalPatch.Edge s) :
    (graph s).dst (oldEdge s e)=oldVertex s ((LocalPatch.numericGraph s).dst e) := by
  cases s
  case wireTop =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireTop e,true)).val)=
      (LocalPatch.edgePair .wireTop e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.WireFramed.retained_target (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case wireBottom =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireBottom e,true)).val)=
      (LocalPatch.edgePair .wireBottom e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.WireFramed.retained_target (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case wireDown =>
    apply Fin.ext
    change ColoringMacroFaces.WireFramed.hostValue ((dartIndexEquiv 1323 (oldEdge .wireDown e,true)).val)=
      (LocalPatch.edgePair .wireDown e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.WireFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.WireFramed.retained_target (ColoringWireMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringWireMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringWireMacroEmitterJoin.edgePair_eq e)).symm
  case cross =>
    apply Fin.ext
    change ColoringMacroFaces.CrossFramed.hostValue ((dartIndexEquiv 3168 (oldEdge .cross e,true)).val)=
      (LocalPatch.edgePair .cross e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.CrossFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.CrossFramed.retained_target (ColoringCrossMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringCrossMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringCrossMacroEmitterJoin.edgePair_eq e)).symm
  case fan =>
    apply Fin.ext
    change ColoringMacroFaces.FanFramed.hostValue ((dartIndexEquiv 2632 (oldEdge .fan e,true)).val)=
      (LocalPatch.edgePair .fan e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.FanFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.FanFramed.retained_target (ColoringFanMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringFanMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringFanMacroEmitterJoin.edgePair_eq e)).symm
  case test =>
    apply Fin.ext
    change ColoringMacroFaces.TestFramed.hostValue ((dartIndexEquiv 285 (oldEdge .test e,true)).val)=
      (LocalPatch.edgePair .test e).2
    rw [dartIndexEquiv_val]
    change ColoringMacroFaces.TestFramed.hostValue (2*e.val+1)=_
    have h:=ColoringMacroFaces.TestFramed.retained_target (ColoringTestMacroEmitterJoin.edgeIndex e)
    simp only [Nat.mod_eq_of_lt (ColoringTestMacroEmitterJoin.edgeIndex e).isLt] at h
    exact h.trans (congrArg Prod.snd (ColoringTestMacroEmitterJoin.edgePair_eq e)).symm
end PlanarHom.ColoringEmitter.FramedMacro
