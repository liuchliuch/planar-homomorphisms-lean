import PlanarHom.FixedGadgetNetworkCode
import PlanarHom.ColoredGadgetReindex

/-! NEW reconstruction of literal finite template signatures and their ordinary
outer-face geometry. These definitions retain all private vertices/occurrences;
no replacement algorithm or signature availability is postulated. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedGadgetNetwork
open Complexity
variable {C R : Type} [CommSemiring R] {b p e bt ut : ℕ}

def mergeColor (τ : Fin b→C) (η : Fin p→C) : Fin (b+p)→C :=
  fun v=>Sum.elim τ η (finSumFinEquiv.symm v)

@[simp] theorem mergeColor_left (τ : Fin b→C) (η : Fin p→C) (i : Fin b) :
    mergeColor τ η (Fin.castAdd p i)=τ i := by simp [mergeColor]
@[simp] theorem mergeColor_right (τ : Fin b→C) (η : Fin p→C) (i : Fin p) :
    mergeColor τ η (Fin.natAdd b i)=η i := by simp [mergeColor]

def factor (g : MixedCode) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (σ : Fin g.vertices→C) : R :=
  (g.edges.map (MixedCode.binaryValue g.vertices bt M σ)).prod *
    (g.unaries.map (MixedCode.unaryValue g.vertices ut U σ)).prod

variable [Fintype C]

def templateSignature (t : Template) (M : Fin bt→Matrix C C R) (U : Fin ut→C→R)
    (τ : Fin t.boundary→C) : R :=
  ∑ η : Fin t.privateCount→C,factor t.code M U (mergeColor τ η)

def twoTerminalFinGraph (G : TwoTerminal (Fin p) (Fin e)) : MultiGraph (Fin 2⊕Fin p) (Fin e) :=
  G.reindex (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) (Equiv.refl _)

def Template.terminalVertices (t : Template) (hb : t.boundary=2) :
    Bool⊕Fin t.privateCount ≃ Fin (t.boundary+t.privateCount) :=
  ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (congrArg (·+t.privateCount) hb.symm))

def Template.edgeGadget (t : Template) (hb : t.boundary=2) (ht : t.code.Valid bt ut) :
    TwoTerminal (Fin t.privateCount) (Fin t.edges.length) :=
  (t.code.toMultiGraph ht).reindex (t.terminalVertices hb).symm (Equiv.refl _)

def ofColoredFinGraph (G : MultiGraph (Fin b⊕Fin p) (Fin e)) (label : Fin e→Fin bt) : Template where
  boundary := b
  privateCount := p
  edges := List.ofFn (fun i=>((finSumFinEquiv (G.src i)).val,
    (finSumFinEquiv (G.dst i)).val,(label i).val))
  unaries := []

def ofColoredTwoTerminal (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt) : Template :=
  ofColoredFinGraph (twoTerminalFinGraph G) label

@[simp] theorem ofColoredTwoTerminal_boundary (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) : (ofColoredTwoTerminal G label).boundary=2 := rfl

theorem ofColoredFinGraph_valid (G : MultiGraph (Fin b⊕Fin p) (Fin e)) (label : Fin e→Fin bt) :
    (ofColoredFinGraph G label).code.Valid bt ut := by
  constructor
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨(finSumFinEquiv (G.src i)).isLt,(finSumFinEquiv (G.dst i)).isLt,(label i).isLt⟩
  · simp [ofColoredFinGraph,Template.code]

theorem ofColoredTwoTerminal_valid (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt) :
    (ofColoredTwoTerminal G label).code.Valid bt ut := ofColoredFinGraph_valid _ _

def ofColoredFinGraphIncidenceEquiv (G : MultiGraph (Fin b⊕Fin p) (Fin e)) (label : Fin e→Fin bt) :
    MultiGraph.IncidenceEquiv G ((ofColoredFinGraph G label).code.toMultiGraph
      (ofColoredFinGraph_valid (ut:=ut) G label)) where
  vertex := finSumFinEquiv
  edge := finCongr (by simp [ofColoredFinGraph,Template.code])
  src_eq i := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,ofColoredFinGraph,Template.code,List.get_eq_getElem]
  dst_eq i := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,ofColoredFinGraph,Template.code,List.get_eq_getElem]

def coloredEdgeTemplateIncidence (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin bt) :
    MultiGraph.IncidenceEquiv G ((ofColoredTwoTerminal G label).edgeGadget rfl
      (ofColoredTwoTerminal_valid (ut:=ut) G label)) :=
  ((G.reindexEquiv (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) (Equiv.refl _)).trans
    (ofColoredFinGraphIncidenceEquiv (ut:=ut) (twoTerminalFinGraph G) label)).trans
      (((ofColoredTwoTerminal G label).code.toMultiGraph
        (ofColoredTwoTerminal_valid (ut:=ut) G label)).reindexEquiv
          ((ofColoredTwoTerminal G label).terminalVertices rfl).symm (Equiv.refl _))

@[simp] theorem coloredEdgeTemplateIncidence_terminal (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (v : Bool) :
    (coloredEdgeTemplateIncidence (ut:=ut) G label).vertex (.inl v)=.inl v := by
  cases v <;> rfl

theorem ofColoredTwoTerminal_planar (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (hG : TwoTerminal.PlanarEdgeGadget G) :
    TwoTerminal.PlanarEdgeGadget ((ofColoredTwoTerminal G label).edgeGadget rfl
      (ofColoredTwoTerminal_valid (ut:=ut) G label)) := by
  obtain ⟨d,hd⟩ := hG
  let i := coloredEdgeTemplateIncidence (ut:=ut) G label
  refine ⟨d.transport i,?_⟩
  have h := (d.outerCofacial_transport_iff i (.inl false) (.inl true)).mpr hd
  simpa only [i,coloredEdgeTemplateIncidence_terminal] using h

end PlanarHom.FixedGadgetNetwork
