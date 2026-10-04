import PlanarHom.RoutingClauseRenumbering

/-! The drawn macro-grid is identified occurrence by occurrence with the actual
materialized numeric formula. This closes its genuine incidence planarity. -/
noncomputable section
open Classical
namespace PlanarHom.NumericFormulaIncidence
open ParsimoniousNorOneInThree

def coordinate {V : Type} (c : Clause V) : Fin 3 → V := ![c.1,c.2.1,c.2.2]

def clauseVariable (f : NumericFormula) (hf : NumericValid f) (c : Fin f.2.length) (i : Fin 3) : Fin f.1 :=
  ⟨coordinate (f.2.get c) i,by
    have h := hf (f.2.get c) (List.get_mem _ _)
    fin_cases i
    · exact h.1
    · exact h.2.1
    · exact h.2.2⟩

def graph (f : NumericFormula) (hf : NumericValid f) :
    MultiGraph (Fin f.1 ⊕ Fin f.2.length) (Fin f.2.length × Fin 3) where
  src e := .inl (clauseVariable f hf e.1 e.2)
  dst e := .inr e.1

end PlanarHom.NumericFormulaIncidence

namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree ParsimoniousBlockTemplate MultiGraph

abbrev GridVertex (f : NumericFormula) := Boundary f ⊕ (i : CanvasIndex f) × PatchInternal f i

def mergeGridVertices (f : NumericFormula) : (BooleanGrid f ⊕ ClauseSlots f) ≃ GridVertex f where
  toFun
    | .inl (.inl b) => .inl b
    | .inl (.inr p) => .inr ⟨p.1,.inl p.2⟩
    | .inr p => .inr ⟨p.1,.inr p.2⟩
  invFun
    | .inl b => .inl (.inl b)
    | .inr ⟨i,.inl v⟩ => .inl (.inr ⟨i,v⟩)
    | .inr ⟨i,.inr c⟩ => .inr ⟨i,c⟩
  left_inv := by rintro ((b | ⟨i,v⟩) | ⟨i,c⟩) <;> rfl
  right_inv := by rintro (b | ⟨i,(v | c)⟩) <;> rfl

def localRawVariable (s : CellShape) (v : Fin s.kind.variableCount) : Fin s.portCount ⊕ s.Internal :=
  if h : v.val<s.portCount then .inl ⟨v.val,h⟩
  else .inr (.inl ⟨v.val-s.portCount,by
    have hv := v.isLt
    dsimp [CellShape.auxiliaryCount]
    omega⟩)

theorem vertexEquiv_localRaw (s : CellShape) (v : Fin s.kind.variableCount) :
    s.vertexEquiv (localRawVariable s v)=.inl v := by
  unfold localRawVariable
  split
  · rw [CellShape.vertexEquiv_port]
    apply congrArg Sum.inl
    apply Fin.ext
    rfl
  · rw [CellShape.vertexEquiv_auxiliary]
    apply congrArg Sum.inl
    apply Fin.ext
    simp only
    omega

theorem vertexEquiv_symm_variable (s : CellShape) (v : Fin s.kind.variableCount) :
    s.vertexEquiv.symm (.inl v)=localRawVariable s v := by
  rw [←vertexEquiv_localRaw s v,Equiv.symm_apply_apply]

def localBoolean (f : NumericFormula) (i : CanvasIndex f) (v : Fin (canvasCell f i).shape.kind.variableCount) : BooleanGrid f :=
  if h : v.val<(canvasCell f i).shape.portCount then .inl (boundaryPort f i ⟨v.val,h⟩)
  else .inr ⟨i,⟨v.val-(canvasCell f i).shape.portCount,by
    have hv := v.isLt
    dsimp [CellShape.auxiliaryCount]
    omega⟩⟩

theorem localBoolean_name (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (v : Fin (canvasCell f i).shape.kind.variableCount) :
    booleanName f hf (localBoolean f i v)=
      (canvasCell f i).instruction.1.template.translate (canvasCell f i).base (refs (canvasCell f i).instruction) v := by
  unfold localBoolean
  split
  · rename_i h
    rw [booleanName,boundaryName_port,←Cell.port_reference]
    congr 1
  · rename_i h
    simp only [booleanName]
    have hi := (canvasCell f i).shape.inputs_le_ports
    have hv : ¬v.val<(canvasCell f i).shape.kind.template.inputs := by omega
    simp only [Template.translate,Cell.instruction,dif_neg hv]
    dsimp [CellShape.outputCount]
    omega

theorem localBoolean_vertex (f : NumericFormula) (i : CanvasIndex f)
    (v : Fin (canvasCell f i).shape.kind.variableCount) :
    mergeGridVertices f (.inl (localBoolean f i v))=
      PortPatchAssembly.placeVertex (boundaryPort f) i ((canvasCell f i).shape.vertexEquiv.symm (.inl v)) := by
  rw [vertexEquiv_symm_variable]
  unfold localBoolean localRawVariable
  split <;> rfl

def numericVertexEquiv (f : NumericFormula) (hf : NumericValid f) :
    (Fin (PositiveRoutingCompiler.compile f).1 ⊕ Fin (PositiveRoutingCompiler.compile f).2.length) ≃ GridVertex f :=
  (Equiv.sumCongr (variableEquiv f hf) (clauseAllocation f hf).symm).trans (mergeGridVertices f)

def numericEdgeEquiv (f : NumericFormula) (hf : NumericValid f) :
    (Fin (PositiveRoutingCompiler.compile f).2.length × Fin 3) ≃
      ((i : CanvasIndex f) × PatchEdge f i) where
  toFun e := let p := (clauseAllocation f hf).symm e.1; ⟨p.1,(p.2,e.2)⟩
  invFun e := ((clauseAllocation f hf) ⟨e.1,e.2.1⟩,e.2.2)
  left_inv e := by
    rcases e with ⟨c,k⟩
    change ((clauseAllocation f hf) ((clauseAllocation f hf).symm c),k)=(c,k)
    rw [Equiv.apply_symm_apply]
  right_inv e := by
    rcases e with ⟨i,j,k⟩
    change (let p := (clauseAllocation f hf).symm ((clauseAllocation f hf) ⟨i,j⟩); (⟨p.1,(p.2,k)⟩ : (i : CanvasIndex f) × PatchEdge f i))=⟨i,(j,k)⟩
    rw [Equiv.symm_apply_apply]

@[simp] theorem numericEdgeEquiv_at (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (j : Fin (canvasCell f i).shape.kind.clauseCount) (k : Fin 3) :
    numericEdgeEquiv f hf ((clauseAllocation f hf) ⟨i,j⟩,k)=⟨i,(j,k)⟩ := by
  change (let p := (clauseAllocation f hf).symm ((clauseAllocation f hf) ⟨i,j⟩); (⟨p.1,(p.2,k)⟩ : (i : CanvasIndex f) × PatchEdge f i))=⟨i,(j,k)⟩
  rw [Equiv.symm_apply_apply]

/-- Actual incidence sources agree under the finite variable and clause maps. -/
theorem numeric_src_at (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (j : Fin (canvasCell f i).shape.kind.clauseCount) (k : Fin 3) :
    numericVertexEquiv f hf
      ((NumericFormulaIncidence.graph (PositiveRoutingCompiler.compile f) (PositiveRoutingCompiler.compile_valid f hf)).src
        ((clauseAllocation f hf) ⟨i,j⟩,k))=
      (gridGraph f).src ⟨i,(j,k)⟩ := by
  let v := (canvasCell f i).shape.kind.occurrence j k
  change _=PortPatchAssembly.placeVertex (W := PatchInternal f) (boundaryPort f) i ((canvasCell f i).shape.vertexEquiv.symm (.inl v))
  rw [←localBoolean_vertex f i v]
  apply congrArg (mergeGridVertices f)
  apply congrArg Sum.inl
  apply booleanName_injective f hf
  rw [variableEquiv_name,localBoolean_name]
  change NumericFormulaIncidence.coordinate
      ((PositiveRoutingCompiler.compile f).2.get ((clauseAllocation f hf) ⟨i,j⟩)) k=_
  rw [clauseAllocation_get]
  fin_cases k <;> rfl

theorem numeric_src (f : NumericFormula) (hf : NumericValid f)
    (e : Fin (PositiveRoutingCompiler.compile f).2.length × Fin 3) :
    numericVertexEquiv f hf
      ((NumericFormulaIncidence.graph (PositiveRoutingCompiler.compile f) (PositiveRoutingCompiler.compile_valid f hf)).src e)=
      (gridGraph f).src (numericEdgeEquiv f hf e) := by
  rcases e with ⟨c,k⟩
  obtain ⟨⟨i,j⟩,rfl⟩ := (clauseAllocation f hf).surjective c
  rw [numericEdgeEquiv_at]
  exact numeric_src_at f hf i j k

theorem numeric_dst (f : NumericFormula) (hf : NumericValid f)
    (e : Fin (PositiveRoutingCompiler.compile f).2.length × Fin 3) :
    numericVertexEquiv f hf
      ((NumericFormulaIncidence.graph (PositiveRoutingCompiler.compile f) (PositiveRoutingCompiler.compile_valid f hf)).dst e)=
      (gridGraph f).dst (numericEdgeEquiv f hf e) := by
  rcases e with ⟨c,k⟩
  obtain ⟨⟨i,j⟩,rfl⟩ := (clauseAllocation f hf).surjective c
  rw [numericEdgeEquiv_at]
  change mergeGridVertices f (.inr ((clauseAllocation f hf).symm ((clauseAllocation f hf) ⟨i,j⟩)))=_
  rw [Equiv.symm_apply_apply]
  change Sum.inr ⟨i,Sum.inr j⟩=PortPatchAssembly.placeVertex (W := PatchInternal f) (boundaryPort f) i
    ((canvasCell f i).shape.vertexEquiv.symm (.inr j))
  rw [←CellShape.vertexEquiv_clause,Equiv.symm_apply_apply]
  rfl

/-- The literal emitted numeric formula has a genuine plane incidence drawing,
with every clause occurrence separately represented. -/
def numericDrawing (f : NumericFormula) (hf : NumericValid f) :
    PlaneDrawing (NumericFormulaIncidence.graph (PositiveRoutingCompiler.compile f) (PositiveRoutingCompiler.compile_valid f hf)) where
  point := (gridDrawing f).point ∘ numericVertexEquiv f hf
  point_injective := (gridDrawing f).point_injective.comp (numericVertexEquiv f hf).injective
  curve e := (gridDrawing f).curve (numericEdgeEquiv f hf e)
  curve_zero e := by rw [(gridDrawing f).curve_zero,←numeric_src f hf e]; rfl
  curve_one e := by rw [(gridDrawing f).curve_one,←numeric_dst f hf e]; rfl
  interior_injective e g s t hs ht h := by
    obtain ⟨heg,hst⟩ := (gridDrawing f).interior_injective _ _ s t hs ht h
    exact ⟨(numericEdgeEquiv f hf).injective heg,hst⟩
  interior_avoids e t ht v h := (gridDrawing f).interior_avoids _ t ht (numericVertexEquiv f hf v) h

theorem compile_planar (f : NumericFormula) (hf : NumericValid f) :
    (NumericFormulaIncidence.graph (PositiveRoutingCompiler.compile f) (PositiveRoutingCompiler.compile_valid f hf)).Planar :=
  ⟨numericDrawing f hf⟩

end PlanarHom.PositiveBlockProgram
