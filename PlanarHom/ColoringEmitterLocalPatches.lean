import PlanarHom.ColoringEmitterAllocation
import PlanarHom.RoutingVariableRenumbering
import PlanarHom.PortPatchAssembly

/-! NEW canonical local typed patches of the frozen numeric coloring macros.
A port consists of a source Boolean port and its primary/gray/black channel;
every other literal numeric macro vertex is privately owned by its cell. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter
open MultiGraph PositiveBlockProgram
namespace LocalPatch

abbrev Port (s : CellShape) := Fin s.portCount × Fin 3
abbrev NumericVertex (s : CellShape) := Fin (Macro.vertexCount s.kind)
abbrev Edge (s : CellShape) := Fin (Macro.edges s.kind).length

def portNumber (s : CellShape) (p : Port s) : ℕ :=
  let ids := (Macro.ports s.kind)[p.1.val]?.getD (0,0,0)
  if p.2.val=0 then ids.1 else if p.2.val=1 then ids.2.1 else ids.2.2

theorem portNumber_lt (s : CellShape) : ∀p : Port s,portNumber s p<Macro.vertexCount s.kind := by
  cases s <;> decide +kernel

def portVertex (s : CellShape) (p : Port s) : NumericVertex s := ⟨portNumber s p,portNumber_lt s p⟩

theorem portVertex_injective (s : CellShape) : Function.Injective (portVertex s) := by
  cases s <;> decide +kernel

/-- The literal finite complement of all exposed triple vertices. -/
abbrev Private (s : CellShape) := {v : NumericVertex s // v∉Set.range (portVertex s)}

def localVertexParts (s : CellShape) : (Port s ⊕ Private s) ≃ NumericVertex s :=
  Equiv.ofBijective (Sum.elim (portVertex s) Subtype.val) (by
    constructor
    · intro a b he
      cases a with
      | inl a =>
        cases b with
        | inl b => exact congrArg Sum.inl (portVertex_injective s he)
        | inr b => exact False.elim (b.property ⟨a,he⟩)
      | inr a =>
        cases b with
        | inl b => exact False.elim (a.property ⟨b,he.symm⟩)
        | inr b => exact congrArg Sum.inr (Subtype.ext he)
    · intro v
      by_cases hv:v∈Set.range (portVertex s)
      · obtain ⟨p,hp⟩:=hv
        exact ⟨.inl p,hp⟩
      · exact ⟨.inr ⟨v,hv⟩,rfl⟩)

@[simp] theorem localVertexParts_port (s : CellShape) (p : Port s) :
    localVertexParts s (.inl p)=portVertex s p := rfl
@[simp] theorem localVertexParts_private (s : CellShape) (w : Private s) :
    localVertexParts s (.inr w)=w.val := rfl

def edgePair (s : CellShape) (e : Edge s) : ℕ×ℕ := (Macro.edges s.kind).get e

theorem edgePair_bounds (s : CellShape) (e : Edge s) :
    (edgePair s e).1<Macro.vertexCount s.kind ∧ (edgePair s e).2<Macro.vertexCount s.kind :=
  Macro.edges_valid s.kind _ (List.get_mem _ _)

def numericGraph (s : CellShape) : MultiGraph (NumericVertex s) (Edge s) where
  src e := ⟨(edgePair s e).1,(edgePair_bounds s e).1⟩
  dst e := ⟨(edgePair s e).2,(edgePair_bounds s e).2⟩

def graph (s : CellShape) : MultiGraph (Port s ⊕ Private s) (Edge s) where
  src e := (localVertexParts s).symm ((numericGraph s).src e)
  dst e := (localVertexParts s).symm ((numericGraph s).dst e)

@[simp] theorem graph_source (s : CellShape) (e : Edge s) :
    localVertexParts s ((graph s).src e)=(numericGraph s).src e :=
  (localVertexParts s).apply_symm_apply _
@[simp] theorem graph_target (s : CellShape) (e : Edge s) :
    localVertexParts s ((graph s).dst e)=(numericGraph s).dst e :=
  (localVertexParts s).apply_symm_apply _

end LocalPatch
end PlanarHom.ColoringEmitter
