import PlanarHom.RoutingCellSeparation
import PlanarHom.PortPatchAssembly

/-! A finite, actual plane-drawn macro-grid incidence graph for the generated
canvas. Boundary vertices are precisely used signal grid points plus original
inputs; no infinitely many grid vertices or phantom signal ports are included. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open MultiGraph ParsimoniousNorOneInThree

def CellShape.auxiliaryCount (s : CellShape) : ℕ := s.kind.variableCount-s.portCount
abbrev CellShape.Internal (s : CellShape) := Fin s.auxiliaryCount ⊕ Fin s.kind.clauseCount

def CellShape.variableEquiv (s : CellShape) :
    (Fin s.portCount ⊕ Fin s.auxiliaryCount) ≃ Fin s.kind.variableCount :=
  finSumFinEquiv.trans (finCongr (Nat.add_sub_of_le s.portCount_le))

def CellShape.vertexEquiv (s : CellShape) :
    (Fin s.portCount ⊕ s.Internal) ≃ (Fin s.kind.variableCount ⊕ Fin s.kind.clauseCount) :=
  (Equiv.sumAssoc _ _ _).symm.trans (Equiv.sumCongr s.variableEquiv (Equiv.refl _))

@[simp] theorem CellShape.vertexEquiv_port (s : CellShape) (i : Fin s.portCount) :
    s.vertexEquiv (.inl i)=.inl (s.portVertex i) := by
  apply congrArg Sum.inl
  apply Fin.ext
  rfl

@[simp] theorem CellShape.vertexEquiv_auxiliary (s : CellShape) (i : Fin s.auxiliaryCount) :
    s.vertexEquiv (.inr (.inl i))=.inl ⟨s.portCount+i.val,by
      have h := i.isLt; dsimp [CellShape.auxiliaryCount] at h; omega⟩ := by
  apply congrArg Sum.inl
  apply Fin.ext
  rfl

@[simp] theorem CellShape.vertexEquiv_clause (s : CellShape) (i : Fin s.kind.clauseCount) :
    s.vertexEquiv (.inr (.inr i))=.inr i := rfl

def CellShape.patchGraph (s : CellShape) :
    MultiGraph (Fin s.portCount ⊕ s.Internal) (Fin s.kind.clauseCount × Fin 3) where
  src e := s.vertexEquiv.symm (s.kind.incidence.src e)
  dst e := s.vertexEquiv.symm (s.kind.incidence.dst e)

def Cell.patchDrawing (c : Cell) : PlaneDrawing c.shape.patchGraph where
  point := c.placedDrawing.point ∘ c.shape.vertexEquiv
  point_injective := c.placedDrawing.point_injective.comp c.shape.vertexEquiv.injective
  curve := c.placedDrawing.curve
  curve_zero e := by simp [CellShape.patchGraph,c.placedDrawing.curve_zero]
  curve_one e := by simp [CellShape.patchGraph,c.placedDrawing.curve_one]
  interior_injective := c.placedDrawing.interior_injective
  interior_avoids e t ht v := c.placedDrawing.interior_avoids e t ht (c.shape.vertexEquiv v)

theorem Cell.patch_port (c : Cell) (i : Fin c.shape.portCount) :
    c.patchDrawing.point (.inl i)=gridPoint (c.portData i).2.1 (c.portData i).2.2 := by
  simp only [Cell.patchDrawing,Function.comp_apply,CellShape.vertexEquiv_port]
  exact c.placed_port i

theorem Cell.patch_internal (c : Cell) (v : c.shape.Internal) : c.patchDrawing.point (.inr v)∈c.region := by
  cases v with
  | inl v =>
    simp only [Cell.patchDrawing,Function.comp_apply,CellShape.vertexEquiv_auxiliary]
    exact c.auxiliary_in_region _ (by simp)
  | inr v =>
    simp only [Cell.patchDrawing,Function.comp_apply,CellShape.vertexEquiv_clause]
    exact c.clause_in_region v

def canvasCell (f : NumericFormula) (i : Fin (canvas f).length) : Cell := (canvas f).get i

/-- The exact finite set of geometrically used signal coordinates. Original
inputs are retained even if the formula is empty or a variable is unused. -/
def boundaryPositions (f : NumericFormula) : Finset (ℕ × ℕ) :=
  Finset.univ.image (fun i : Fin f.1 => (0,i.val)) ∪
    Finset.univ.biUnion (fun i : Fin (canvas f).length =>
      Finset.univ.image (fun k : Fin (canvasCell f i).shape.portCount => ((canvasCell f i).portData k).2))

abbrev Boundary (f : NumericFormula) := ↥(boundaryPositions f)
abbrev CanvasIndex (f : NumericFormula) := Fin (canvas f).length
abbrev PatchInternal (f : NumericFormula) (i : CanvasIndex f) := (canvasCell f i).shape.Internal
abbrev PatchEdge (f : NumericFormula) (i : CanvasIndex f) := Fin (canvasCell f i).shape.kind.clauseCount × Fin 3
abbrev PatchPort (f : NumericFormula) (i : CanvasIndex f) := Fin (canvasCell f i).shape.portCount

def boundaryPort (f : NumericFormula) (i : CanvasIndex f) (k : PatchPort f i) : Boundary f :=
  ⟨((canvasCell f i).portData k).2,by
    apply Finset.mem_union_right
    apply Finset.mem_biUnion.mpr
    exact ⟨i,Finset.mem_univ _,Finset.mem_image.mpr ⟨k,Finset.mem_univ _,rfl⟩⟩⟩

def boundaryPoint (f : NumericFormula) (b : Boundary f) : Plane := gridPoint b.val.1 b.val.2

theorem boundaryPoint_injective (f : NumericFormula) : Function.Injective (boundaryPoint f) := by
  intro p q h
  apply Subtype.ext
  apply Prod.ext
  · have hh := congrArg Prod.fst h
    dsimp [boundaryPoint,gridPoint] at hh
    exact_mod_cast (show (p.val.1:ℝ)=q.val.1 by linarith)
  · have hh := congrArg Prod.snd h
    dsimp [boundaryPoint,gridPoint] at hh
    exact_mod_cast (show (p.val.2:ℝ)=q.val.2 by linarith)

/-- The finite graph obtained by the literal coordinate-identification of cell
ports. Its vertices are signal ports, Boolean auxiliaries, and clause nodes. -/
def gridGraph (f : NumericFormula) :
    MultiGraph (Boundary f ⊕ (i : CanvasIndex f) × PatchInternal f i) ((i : CanvasIndex f) × PatchEdge f i) :=
  PortPatchAssembly.graph (fun i => (canvasCell f i).shape.patchGraph) (boundaryPort f)

/-- Full actual global drawing of the concrete emitted cell canvas. The
numeric-index / Boolean-assignment correspondence is a separate bridge. -/
def gridDrawing (f : NumericFormula) : PlaneDrawing (gridGraph f) := by
  apply PortPatchAssembly.drawing
    (fun i : CanvasIndex f => (canvasCell f i).shape.patchGraph)
    (fun i => (canvasCell f i).patchDrawing)
    (fun i => (canvasCell f i).region)
    (boundaryPoint f) (boundaryPort f)
  · exact canvas_regions_disjoint f
  · exact boundaryPoint_injective f
  · intro i b
    exact (canvasCell f i).gridPoint_outside b.val.1 b.val.2
  · intro i w
    exact (canvasCell f i).patch_internal w
  · intro i e t ht
    exact (canvasCell f i).curve_in_region e t ht
  · intro i k
    exact (canvasCell f i).patch_port k

theorem grid_planar (f : NumericFormula) : (gridGraph f).Planar := ⟨gridDrawing f⟩

end PlanarHom.PositiveBlockProgram
