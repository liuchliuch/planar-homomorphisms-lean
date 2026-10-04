import PlanarHom.SignedNandCanvas
import PlanarHom.PlaneDrawingEdgeKeys

/-! Every numeric signed-NAND adjacency is an actual drawn canvas edge. The
finite vertex map retains exactly the routed Boolean variables and centers. -/
noncomputable section
open Classical
namespace PlanarHom.SignedNandNumeric
open Complexity ParsimoniousNorOneInThree PositiveBlockProgram SignedNandCells MultiGraph

abbrev Routed (f : NumericFormula) := PositiveRoutingCompiler.compile f

def canvasNumber (f : NumericFormula) (hf : NumericValid f) :
    GridVertex f ≃ Fin ((Routed f).1+(Routed f).2.length) :=
  (numericVertexEquiv f hf).symm.trans finSumFinEquiv

def localVertex (f : NumericFormula) (i : CanvasIndex f) (v : SignedNandCells.Vertex (canvasCell f i).shape.kind) : GridVertex f :=
  PortPatchAssembly.placeVertex (boundaryPort f) i ((canvasCell f i).shape.vertexEquiv.symm v)

theorem canvasNumber_variable (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (v : Fin (canvasCell f i).shape.kind.variableCount) :
    (canvasNumber f hf (localVertex f i (.inl v))).val=
      (canvasCell f i).instruction.1.template.translate (canvasCell f i).base (refs (canvasCell f i).instruction) v := by
  unfold localVertex
  rw [←localBoolean_vertex]
  simp only [canvasNumber,numericVertexEquiv,Equiv.symm_trans_apply,Equiv.trans_apply,Equiv.symm_apply_apply]
  change ((variableEquiv f hf).symm (localBoolean f i v)).val=_
  have h := variableEquiv_name f hf ((variableEquiv f hf).symm (localBoolean f i v))
  rw [Equiv.apply_symm_apply,localBoolean_name] at h
  exact h.symm

theorem canvasNumber_center (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (j : Fin (canvasCell f i).shape.kind.clauseCount) :
    (canvasNumber f hf (localVertex f i (.inr j))).val=
      (Routed f).1+(clauseAllocation f hf ⟨i,j⟩).val := by
  unfold localVertex
  rw [←CellShape.vertexEquiv_clause,Equiv.symm_apply_apply]
  rfl

def clauseEdgeAt (n : ℕ) (p : Clause ℕ × ℕ) : Fin 6 → Edge :=
  ![(p.1.1,p.1.2.1),(p.1.2.1,p.1.2.2),(p.1.2.2,p.1.1),
    (p.1.1,n+p.2),(p.1.2.1,n+p.2),(p.1.2.2,n+p.2)]

theorem clauseEdges_eq (n : ℕ) (p : Clause ℕ × ℕ) : clauseEdges n p=List.ofFn (clauseEdgeAt n p) := rfl

theorem local_raw_numbers (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (j : Fin (canvasCell f i).shape.kind.clauseCount) (t : Fin 6) :
    ((canvasNumber f hf (localVertex f i ((rawGraph (canvasCell f i).shape.kind).src (j,t)))).val,
     (canvasNumber f hf (localVertex f i ((rawGraph (canvasCell f i).shape.kind).dst (j,t)))).val)=
      clauseEdgeAt (Routed f).1 ((canvasCell f i).numericClause j,(clauseAllocation f hf ⟨i,j⟩).val) t := by
  fin_cases t
  all_goals simp [rawGraph,SignedNandFormulaIdentity.graph,Matrix.cons_val_zero,Matrix.cons_val_succ,
    canvasNumber_variable,canvasNumber_center,clauseEdgeAt,Kind.occurrence,Cell.numericClause]

theorem rawEdges_index (g : NumericFormula) (r : Edge) (hr : r∈rawEdges g) :
    ∃c : Fin g.2.length,∃t : Fin 6,r=clauseEdgeAt g.1 (g.2.get c,c.val) t := by
  obtain ⟨⟨c,j⟩,hc,hr⟩ := List.mem_flatMap.mp hr
  have hj : j<g.2.length := by simpa using List.snd_lt_of_mem_zipIdx hc
  have hc' : c=g.2.get ⟨j,hj⟩ := by simpa using List.fst_eq_of_mem_zipIdx hc
  rw [clauseEdges_eq] at hr
  obtain ⟨t,ht⟩ := List.mem_ofFn.mp hr
  exact ⟨⟨j,hj⟩,t,by simpa only [hc'] using ht.symm⟩

/-- Normalized local K4 occurrences have matching actual canvas curves. -/
theorem canvas_coverage_at (f : NumericFormula) (hf : NumericValid f) (i : CanvasIndex f)
    (j : Fin (canvasCell f i).shape.kind.clauseCount) (t : Fin 6) :
    ∃e : (i : CanvasIndex f) × CanvasEdge f i,
      graphEdgeKey (canvasGraph f) (canvasNumber f hf) e=
        normalize (clauseEdgeAt (Routed f).1 ((canvasCell f i).numericClause j,
          (clauseAllocation f hf ⟨i,j⟩).val) t) := by
  obtain ⟨e,he⟩ := edge_coverage (canvasCell f i).shape.kind j t
  refine ⟨⟨i,e⟩,?_⟩
  change normalize ((canvasNumber f hf (localVertex f i ((SignedNandCells.graph _).src e))).val,
    (canvasNumber f hf (localVertex f i ((SignedNandCells.graph _).dst e))).val)=_
  rcases he with ⟨hs,hd⟩ | ⟨hs,hd⟩
  · rw [hs,hd,local_raw_numbers]
  · rw [hs,hd]
    rw [normalize_swap ((canvasNumber f hf (localVertex f i ((rawGraph (canvasCell f i).shape.kind).src (j,t)))).val,
      (canvasNumber f hf (localVertex f i ((rawGraph (canvasCell f i).shape.kind).dst (j,t)))).val)]
    rw [local_raw_numbers]

/-- Full materialized code adjacency is covered by the concrete global drawing. -/
theorem canvas_coverage (f : NumericFormula) (hf : NumericValid f) (e : Edge) (he : e∈edges (Routed f)) :
    ∃a,graphEdgeKey (canvasGraph f) (canvasNumber f hf) a=e := by
  obtain ⟨r,hr,rfl⟩ := normalized_mem (Routed f) e he
  obtain ⟨c,t,rfl⟩ := rawEdges_index (Routed f) r hr
  obtain ⟨⟨i,j⟩,rfl⟩ := (clauseAllocation f hf).surjective c
  rw [clauseAllocation_get]
  exact canvas_coverage_at f hf i j t

theorem edges_bound (g : NumericFormula) (hg : NumericValid g) :
    ∀e∈edges g,e.1<g.1+g.2.length ∧ e.2<g.1+g.2.length := by
  intro e he
  have h := (compile_valid g hg).1 (e.1,e.2,0) (List.mem_map.mpr ⟨e,he,rfl⟩)
  exact ⟨h.1,h.2.1⟩

def codeIncidenceEquiv (g : NumericFormula) (hg : NumericValid g) :
    IncidenceEquiv (listGraph (edges g) (edges_bound g hg)) ((compile g).toMultiGraph (compile_valid g hg)) where
  vertex := Equiv.refl _
  edge := finCongr (by simp [compile])
  src_eq e := by apply Fin.ext; simp [MixedCode.toMultiGraph,compile,listGraph,List.get_eq_getElem]
  dst_eq e := by apply Fin.ext; simp [MixedCode.toMultiGraph,compile,listGraph,List.get_eq_getElem]

/-- Literal ordinary-plane drawing for the final mixed-code incidence graph.
No input embedding or connectedness certificate is required by the compiler. -/
def compileDrawing (f : NumericFormula) (hf : NumericValid f) :
    PlaneDrawing ((compile (Routed f)).toMultiGraph (compile_valid _ (PositiveRoutingCompiler.compile_valid f hf))) :=
  (drawingFromKeys (canvasGraph f) (canvasNumber f hf) (canvasDrawing f) (edges (Routed f))
    (edges_bound _ (PositiveRoutingCompiler.compile_valid f hf)) (edges_nodup _) (canvas_coverage f hf)).transport
      (codeIncidenceEquiv _ (PositiveRoutingCompiler.compile_valid f hf))

theorem compile_planar (f : NumericFormula) (hf : NumericValid f) : (compile (Routed f)).PlanarValid 1 1 :=
  (MixedCode.planarValid_iff _ (compile_valid _ (PositiveRoutingCompiler.compile_valid f hf))).mpr ⟨compileDrawing f hf⟩

end PlanarHom.SignedNandNumeric
