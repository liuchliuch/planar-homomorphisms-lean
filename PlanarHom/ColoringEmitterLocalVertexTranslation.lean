import PlanarHom.ColoringEmitterVertexEquivalence
import PlanarHom.ColoringEmitterInputAllocation

/-! NEW endpoint transport for each original macro occurrence into its actual
numeric allocation. Shared ports use the persistent signal dictionary. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem port_output_index_lt (s : CellShape) (p : Fin s.portCount)
     (hp:¬p.val<Macro.inputCount s.kind) :
     p.val-Macro.inputCount s.kind<s.outputCount := by
   have h:=s.inputs_add_outputs
   rw [←inputCount_eq] at h
   omega

 theorem vertex_local (f : NumericFormula) (hf:NumericValid f) (i : Index f)
     (v : LocalPatch.Port (canvasCell f i).shape ⊕ Private f i) :
     (vertexEquiv f hf (PortPatchAssembly.placeVertex (port f) i v)).val=
       localVertex (canvasCell f i).instruction (before f i).dictionary (before f i).vertices
         (LocalPatch.localVertexParts (canvasCell f i).shape v).val := by
   cases v with
   | inl p =>
     change (vertexEquiv f hf (.inl (boundaryPort f i p.1,p.2))).val=localVertex _ _ _ (LocalPatch.portNumber _ p)
     rw [vertex_boundary,boundaryName_port]
     simp only [localVertex,Cell.instruction,LocalPatch.port_address]
     by_cases hp:p.1.val<Macro.inputCount (canvasCell f i).shape.kind
     · simp only [if_pos hp,ite_true]
       rw [cell_port_input _ _ hp]
       exact congrArg (fun n=>n+p.2.val) (state_dictionary_before f i _ (by
         rw [before_dictionary_length f hf]
         exact cell_input_lt f hf i _ hp))
     · simp only [if_neg hp,ite_false]
       rw [cell_port_output _ _ hp]
       have h:=state_dictionary_output f hf i
         ⟨p.1.val-Macro.inputCount (canvasCell f i).shape.kind,port_output_index_lt _ _ hp⟩
       simpa only [Fin.val_mk,Nat.add_assoc] using congrArg (fun n=>n+p.2.val) h
   | inr w =>
     change (vertexEquiv f hf (.inr ⟨i,w⟩)).val=localVertex _ _ _ w.val.val
     rw [vertex_private]
     simp only [localVertex,Cell.instruction,LocalPatch.private_address]
     simp [outputs_eq]

end PlanarHom.ColoringEmitter.Canvas
