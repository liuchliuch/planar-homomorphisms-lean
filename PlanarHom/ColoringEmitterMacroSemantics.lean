import PlanarHom.ColoringWireMacroEmitterJoin
import PlanarHom.ColoringCrossMacroEmitterJoin
import PlanarHom.ColoringFanMacroEmitterJoin
import PlanarHom.ColoringTestMacroEmitterJoin
import PlanarHom.ColoringWireMacroSemantics
import PlanarHom.ColoringCrossMacroSemantics
import PlanarHom.ColoringFanMacroSemantics
import PlanarHom.ColoringTestMacroSemantics
import PlanarHom.PalettedPatchConnected

/-! The exact canonical patches consumed by the numeric emitter. All four
coloring equivalences below are transported along checked literal edge tables.
The three wire shapes differ only geometrically, not in their actual graph. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.MacroSemantics
open MultiGraph PositiveBlockProgram ParsimoniousBlockTemplate
open ColoringTemplateBoundaryStates PalettedColoringPatches ThreeColorPaletteCounting

theorem inputs_le_ports (s : CellShape) : s.kind.template.inputs≤s.portCount := by cases s <;> decide

theorem ports_le_variables (s : CellShape) : s.portCount≤s.kind.template.inputs+s.kind.template.fresh := by cases s <;> decide

def accepted (s : CellShape) := Allowed s.kind.template s.portCount (inputs_le_ports s) (ports_le_variables s)

def partsEquiv (s : CellShape) : IncidenceEquiv (LocalPatch.graph s) (LocalPatch.numericGraph s) where
  vertex := LocalPatch.localVertexParts s
  edge := Equiv.refl _
  src_eq e := (LocalPatch.graph_source s e).symm
  dst_eq e := (LocalPatch.graph_target s e).symm

def numericEquiv (s : CellShape) : Coloring (LocalPatch.numericGraph s) ≃ PalettedColoringPatches.State (Fin s.portCount) (accepted s) :=
  match s with
  | .wireTop => ColoringWireMacroEmitterJoin.numericEquiv.colorings.trans ColoringWireMacroSemantics.numericEquiv
  | .wireBottom => ColoringWireMacroEmitterJoin.numericEquiv.colorings.trans ColoringWireMacroSemantics.numericEquiv
  | .wireDown => ColoringWireMacroEmitterJoin.numericEquiv.colorings.trans ColoringWireMacroSemantics.numericEquiv
  | .cross => ColoringCrossMacroEmitterJoin.numericEquiv.colorings.trans ColoringCrossMacroSemantics.numericEquiv
  | .fan => ColoringFanMacroEmitterJoin.numericEquiv.colorings.trans ColoringFanMacroSemantics.numericEquiv
  | .test => ColoringTestMacroEmitterJoin.numericEquiv.colorings.trans ColoringTestMacroSemantics.numericEquiv

def equiv (s : CellShape) : Coloring (LocalPatch.graph s) ≃ PalettedColoringPatches.State (Fin s.portCount) (accepted s) :=
  (partsEquiv s).colorings.trans (numericEquiv s)

theorem numeric_inverse_port (s : CellShape) (a : PalettedColoringPatches.State (Fin s.portCount) (accepted s)) (p : LocalPatch.Port s) :
    ((numericEquiv s).symm a).val (LocalPatch.portVertex s p)=portColor a p := by
  cases s
  case wireTop =>
    change (ColoringWireMacroSemantics.numericEquiv.symm a).val
      (ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireTop p))=_
    rw [ColoringWireMacroEmitterJoin.port_eq]
    exact ColoringWireMacroSemantics.numeric_inverse_port a p.1 p.2
  case wireBottom =>
    change (ColoringWireMacroSemantics.numericEquiv.symm a).val
      (ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireTop p))=_
    rw [ColoringWireMacroEmitterJoin.port_eq]
    exact ColoringWireMacroSemantics.numeric_inverse_port a p.1 p.2
  case wireDown =>
    change (ColoringWireMacroSemantics.numericEquiv.symm a).val
      (ColoringWireMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .wireTop p))=_
    rw [ColoringWireMacroEmitterJoin.port_eq]
    exact ColoringWireMacroSemantics.numeric_inverse_port a p.1 p.2
  case cross =>
    change (ColoringCrossMacroSemantics.numericEquiv.symm a).val
      (ColoringCrossMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .cross p))=_
    rw [ColoringCrossMacroEmitterJoin.port_eq]
    exact ColoringCrossMacroSemantics.numeric_inverse_port a p.1 p.2
  case fan =>
    change (ColoringFanMacroSemantics.numericEquiv.symm a).val
      (ColoringFanMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .fan p))=_
    rw [ColoringFanMacroEmitterJoin.port_eq]
    exact ColoringFanMacroSemantics.numeric_inverse_port a p.1 p.2
  case test =>
    change (ColoringTestMacroSemantics.numericEquiv.symm a).val
      (ColoringTestMacroEmitterJoin.vertexIndex (LocalPatch.portVertex .test p))=_
    rw [ColoringTestMacroEmitterJoin.port_eq]
    exact ColoringTestMacroSemantics.numeric_inverse_port a p.1 p.2

theorem inverse_port (s : CellShape) (a : PalettedColoringPatches.State (Fin s.portCount) (accepted s)) (p : LocalPatch.Port s) :
    ((equiv s).symm a).val (.inl p)=portColor a p := numeric_inverse_port s a p

def patch (s : CellShape) : Patch (Fin s.portCount) (LocalPatch.Private s) (LocalPatch.Edge s) where
  graph := LocalPatch.graph s
  accepted := accepted s
  equiv := equiv s
  ports col p := by
    have h := inverse_port s (equiv s col) p
    simpa only [Equiv.symm_apply_apply] using h

def witnessInput (s : CellShape) : Fin s.kind.template.inputs → Bool :=
  fun i => if s=.test then decide (i.val=0) else false

theorem witnessInput_accepted (s : CellShape) : s.kind.template.accepts (witnessInput s) := by
  cases s <;> simp [CellShape.kind,Kind.template,equality,crossover,fanout,termination,witnessInput,ParsimoniousNorOneInThree.ExactlyOne]

def witnessBits (s : CellShape) : {b : Fin s.portCount → Bool // accepted s b} :=
  boundaryEquiv s.kind.template s.portCount (inputs_le_ports s) (ports_le_variables s)
    ⟨s.kind.template.extend (witnessInput s),extension_satisfies _ _ (witnessInput_accepted s)⟩

instance port_nonempty (s : CellShape) : Nonempty (Fin s.portCount) := by cases s <;> exact ⟨⟨0,by decide⟩⟩

def witness (s : CellShape) : Coloring (LocalPatch.graph s) :=
  (equiv s).symm (⟨(0,1),by decide⟩,witnessBits s)

theorem connected (s : CellShape) (u v : LocalPatch.Port s ⊕ LocalPatch.Private s) :
    (LocalPatch.graph s).componentSetoid Finset.univ u v :=
  (patch s).connected ⟨witness s⟩ u v

theorem incident (s : CellShape) (v : LocalPatch.Port s ⊕ LocalPatch.Private s) :
    ∃e,(LocalPatch.graph s).src e=v ∨ (LocalPatch.graph s).dst e=v :=
  (patch s).incident ⟨witness s⟩ v

end PlanarHom.ColoringEmitter.MacroSemantics
