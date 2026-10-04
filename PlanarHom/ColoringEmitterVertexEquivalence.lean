import PlanarHom.ColoringEmitterPrefixAllocation
import PlanarHom.ColoringEmitterPrivateVertices

/-! NEW exact vertex bijection from the shared palette canvas to the actual
numeric emitter. Every fresh triple and private vertex occupies its own block. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.Canvas
open PositiveBlockProgram ParsimoniousNorOneInThree

def sigmaPair (I : Type) (A : I→Type) (B : Type) :
    ((i:I) × (A i × B)) ≃ ((i:I) × A i) × B where
  toFun p := (⟨p.1,p.2.1⟩,p.2.2)
  invFun p := ⟨p.1.1,p.1.2,p.2⟩
  left_inv p := by rcases p with ⟨i,a,b⟩; rfl
  right_inv p := by rcases p with ⟨⟨i,a⟩,b⟩; rfl

def sumPair (A B C : Type) : ((A×C) ⊕ (B×C)) ≃ ((A⊕B)×C) where
  toFun p := match p with | .inl p=>(.inl p.1,p.2) | .inr p=>(.inr p.1,p.2)
  invFun p := match p.1 with | .inl a=>.inl (a,p.2) | .inr b=>.inr (b,p.2)
  left_inv p := by cases p <;> rfl
  right_inv p := by rcases p with ⟨a,b⟩; cases a <;> rfl

theorem outputs_eq (s : CellShape) : s.outputCount=Macro.outputCount s.kind := by cases s <;> decide

def initialBlock (f : NumericFormula) : Fin (3*f.1) ≃ Fin f.1 × Fin 3 :=
  (finCongr (Nat.mul_comm 3 f.1)).trans finProdFinEquiv.symm

def localBlock (s : CellShape) : Fin (Macro.addedVertices s.kind) ≃
    ((Fin s.outputCount × Fin 3) ⊕ LocalPatch.Private s) :=
  (finCongr (by rw [Macro.addedVertices_eq,outputs_eq,Nat.mul_comm 3])).trans
    (finSumFinEquiv.symm.trans (Equiv.sumCongr finProdFinEquiv.symm (LocalPatch.privateEquiv s).symm))

def vertexParts (f : NumericFormula) (hf : NumericValid f) : Allocation f ≃ Vertex f :=
  (Equiv.sumCongr (initialBlock f) (Equiv.sigmaCongrRight (fun i=>localBlock (canvasCell f i).shape))).trans
    ((Equiv.sumCongr (Equiv.refl _)
      (Equiv.sigmaSumDistrib (fun i:Index f=>Fin (canvasCell f i).shape.outputCount × Fin 3) (Private f))).trans
    ((Equiv.sumAssoc _ _ _).symm.trans
    ((Equiv.sumCongr (Equiv.sumCongr (Equiv.refl _)
      (sigmaPair (Index f) (fun i=>Fin (canvasCell f i).shape.outputCount) (Fin 3))) (Equiv.refl _)).trans
    ((Equiv.sumCongr (sumPair (Fin f.1) ((i:Index f) × Fin (canvasCell f i).shape.outputCount) (Fin 3))
      (Equiv.refl _)).trans
      (Equiv.sumCongr (Equiv.prodCongr (signalEquiv f hf) (Equiv.refl _)) (Equiv.refl _))))))

def vertexEquiv (f : NumericFormula) (hf : NumericValid f) : Vertex f ≃ Fin (state f).vertices :=
  (vertexParts f hf).symm.trans (allocationIndex f)

 theorem vertexEquiv_parts (f : NumericFormula) (hf : NumericValid f) (a : Allocation f) :
     vertexEquiv f hf (vertexParts f hf a)=allocationIndex f a := by simp [vertexEquiv]

 theorem vertexParts_initial (f : NumericFormula) (hf : NumericValid f) (i : Fin f.1) (ch : Fin 3) :
     vertexParts f hf (.inl ((initialBlock f).symm (i,ch)))=.inl (initialBoundary f i,ch) := by
   simp [vertexParts,sigmaPair,sumPair,signalEquiv,allocatedSignal]

 theorem vertexParts_output (f : NumericFormula) (hf : NumericValid f) (i : Index f)
     (j : Fin (canvasCell f i).shape.outputCount) (ch : Fin 3) :
     vertexParts f hf (.inr ⟨i,(localBlock (canvasCell f i).shape).symm (.inl (j,ch))⟩)=
       .inl (boundaryPort f i ((canvasCell f i).freshPort j),ch) := by
   simp [vertexParts,sigmaPair,sumPair,signalEquiv,allocatedSignal]

 theorem vertexParts_private (f : NumericFormula) (hf : NumericValid f) (i : Index f) (w : Private f i) :
     vertexParts f hf (.inr ⟨i,(localBlock (canvasCell f i).shape).symm (.inr w)⟩)=.inr ⟨i,w⟩ := by
   simp [vertexParts,sigmaPair,sumPair]

 theorem initialBlock_symm_val (f : NumericFormula) (i : Fin f.1) (ch : Fin 3) :
     ((initialBlock f).symm (i,ch)).val=3*i.val+ch.val := by
   simp [initialBlock,finProdFinEquiv,Nat.add_comm]

 theorem localBlock_output_val (s : CellShape) (j : Fin s.outputCount) (ch : Fin 3) :
     ((localBlock s).symm (.inl (j,ch))).val=3*j.val+ch.val := by
   simp [localBlock,finProdFinEquiv,Nat.add_comm]

 theorem localBlock_private_val (s : CellShape) (w : LocalPatch.Private s) :
     ((localBlock s).symm (.inr w)).val=3*s.outputCount+(LocalPatch.privateEquiv s w).val := by
   simp [localBlock,Nat.mul_comm]

 theorem vertex_initial (f : NumericFormula) (hf : NumericValid f) (i : Fin f.1) (ch : Fin 3) :
     (vertexEquiv f hf (.inl (initialBoundary f i,ch))).val=3*i.val+ch.val := by
   rw [←vertexParts_initial f hf i ch,vertexEquiv_parts,allocationIndex_initial,initialBlock_symm_val]

 theorem vertex_output (f : NumericFormula) (hf : NumericValid f) (i : Index f)
     (j : Fin (canvasCell f i).shape.outputCount) (ch : Fin 3) :
     (vertexEquiv f hf (.inl (boundaryPort f i ((canvasCell f i).freshPort j),ch))).val=
       (before f i).vertices+3*j.val+ch.val := by
   rw [←vertexParts_output f hf i j ch,vertexEquiv_parts,allocationIndex_new,localBlock_output_val]
   omega

 theorem vertex_private (f : NumericFormula) (hf : NumericValid f) (i : Index f) (w : Private f i) :
     (vertexEquiv f hf (.inr ⟨i,w⟩)).val=(before f i).vertices+3*(canvasCell f i).shape.outputCount+
       (LocalPatch.privateEquiv (canvasCell f i).shape w).val := by
   rw [←vertexParts_private f hf i w,vertexEquiv_parts,allocationIndex_new,localBlock_private_val]
   omega

 theorem vertex_boundary (f : NumericFormula) (hf : NumericValid f) (b : Signal f) (ch : Fin 3) :
     (vertexEquiv f hf (.inl (b,ch))).val=(state f).dictionary[boundaryName f hf b]?.getD 0+ch.val := by
   obtain ⟨a,rfl⟩:=(signalEquiv f hf).surjective b
   cases a with
   | inl i => rw [signalEquiv_initial,vertex_initial,boundaryName_initial,state_dictionary_initial]
   | inr p =>
     rcases p with ⟨i,j⟩
     rw [signalEquiv_output,vertex_output,boundaryName_port,Cell.freshPort_reference,state_dictionary_output f hf]

end PlanarHom.ColoringEmitter.Canvas
