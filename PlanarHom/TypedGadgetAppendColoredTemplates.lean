import PlanarHom.EdgeGadgetTemplateGeometry
import PlanarHom.PrescribedDomains

/-!
Literal serialization of edge-coloured gadgets with a prescribed domain at
 each private vertex. The reserved labels are disjoint from the original
 unary language. Every private vertex contributes exactly one intrinsic
 unary occurrence, and no boundary unary is introduced.
-/

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedGadgetNetwork
open Complexity
variable {b p e bt dt : ℕ}

/-- Edge occurrences keep their labels and private vertices receive one
reserved domain occurrence each. `ut` is the original unary-language size. -/
def ofTypedColoredFinGraph (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) : Template where
  boundary := b
  privateCount := p
  edges := List.ofFn (fun i => ((finSumFinEquiv (G.src i)).val,
    (finSumFinEquiv (G.dst i)).val,(label i).val))
  unaries := List.ofFn (fun j => (b+j.val,ut+(tag j).val))

@[simp] theorem ofTypedColoredFinGraph_unaries_length
    (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredFinGraph G label tag ut).unaries.length=p := by
  simp [ofTypedColoredFinGraph]

@[simp] theorem ofTypedColoredFinGraph_edges_length
    (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredFinGraph G label tag ut).edges.length=e := by
  simp [ofTypedColoredFinGraph]

theorem ofTypedColoredFinGraph_valid (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredFinGraph G label tag ut).code.Valid bt (ut+dt) := by
  constructor
  · intro a ha
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨(finSumFinEquiv (G.src i)).isLt,
      (finSumFinEquiv (G.dst i)).isLt,(label i).isLt⟩
  · intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact ⟨Nat.add_lt_add_left j.isLt b,Nat.add_lt_add_left (tag j).isLt ut⟩

def ofTypedColoredFinGraphIncidenceEquiv
    (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    MultiGraph.IncidenceEquiv G
      ((ofTypedColoredFinGraph G label tag ut).code.toMultiGraph
        (ofTypedColoredFinGraph_valid G label tag ut)) where
  vertex := finSumFinEquiv
  edge := finCongr (by simp [ofTypedColoredFinGraph,Template.code])
  src_eq i := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,ofTypedColoredFinGraph,Template.code,List.get_eq_getElem]
  dst_eq i := by
    apply Fin.ext
    simp [MixedCode.toMultiGraph,ofTypedColoredFinGraph,Template.code,List.get_eq_getElem]

variable {C R : Type} [Fintype C] [CommSemiring R]

omit [Fintype C] in
theorem ofTypedColoredFinGraph_factor (G : MultiGraph (Fin b ⊕ Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ)
    (M : Fin bt → Matrix C C R) (U : Fin (ut+dt) → C → R)
    (τ : Fin b → C) (η : Fin p → C) :
    factor (ofTypedColoredFinGraph G label tag ut).code M U (mergeColor τ η) =
      (∏ j, U (Fin.natAdd ut (tag j)) (η j)) *
        ∏ i, M (label i) (Sum.elim τ η (G.src i)) (Sum.elim τ η (G.dst i)) := by
  have he (i : Fin e) : MixedCode.binaryValue (b+p) bt M (mergeColor τ η)
      ((finSumFinEquiv (G.src i)).val,(finSumFinEquiv (G.dst i)).val,(label i).val) =
      M (label i) (Sum.elim τ η (G.src i)) (Sum.elim τ η (G.dst i)) := by
    simp only [MixedCode.binaryValue,(finSumFinEquiv (G.src i)).isLt,
      (finSumFinEquiv (G.dst i)).isLt,(label i).isLt,and_self,↓reduceDIte]
    simp [mergeColor]
  have hu (j : Fin p) : MixedCode.unaryValue (b+p) (ut+dt) U (mergeColor τ η)
      (b+j.val,ut+(tag j).val) = U (Fin.natAdd ut (tag j)) (η j) := by
    have hj := Nat.add_lt_add_left j.isLt b
    have ht := Nat.add_lt_add_left (tag j).isLt ut
    simp only [MixedCode.unaryValue,hj,ht,and_self,↓reduceDIte]
    exact congrArg (U (Fin.natAdd ut (tag j))) (mergeColor_right τ η j)
  simp only [factor,ofTypedColoredFinGraph,Template.code,List.map_ofFn,List.prod_ofFn,
    Function.comp_def,he,hu]
  exact mul_comm _ _

/-- Literal typed two-terminal serialization, with terminals numbered 0 and 1. -/
def ofTypedColoredTwoTerminal (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) : Template :=
  ofTypedColoredFinGraph (twoTerminalFinGraph G) label tag ut

@[simp] theorem ofTypedColoredTwoTerminal_boundary (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredTwoTerminal G label tag ut).boundary=2 := rfl

@[simp] theorem ofTypedColoredTwoTerminal_privateCount (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredTwoTerminal G label tag ut).privateCount=p := rfl

@[simp] theorem ofTypedColoredTwoTerminal_unaries (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredTwoTerminal G label tag ut).unaries=
      List.ofFn (fun j => (2+j.val,ut+(tag j).val)) := rfl

@[simp] theorem ofTypedColoredTwoTerminal_edges_length (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredTwoTerminal G label tag ut).edges.length=e := by
  simp [ofTypedColoredTwoTerminal]

theorem ofTypedColoredTwoTerminal_valid (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    (ofTypedColoredTwoTerminal G label tag ut).code.Valid bt (ut+dt) :=
  ofTypedColoredFinGraph_valid _ label tag ut

/-- The actual finite sum, with a vertex-dependent private weight. No
assumption on edge labels, supports, signs, or domain intersections is used. -/
theorem ofTypedColoredTwoTerminal_signature (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ)
    (M : Fin bt → Matrix C C R) (U : Fin (ut+dt) → C → R) (τ : Fin 2 → C) :
    templateSignature (ofTypedColoredTwoTerminal G label tag ut) M U τ =
      ∑ η : Fin p → C, (∏ j, U (Fin.natAdd ut (tag j)) (η j)) *
        ∏ i, M (label i) (TwoTerminal.extend (τ 0) (τ 1) η (G.src i))
          (TwoTerminal.extend (τ 0) (τ 1) η (G.dst i)) := by
  unfold templateSignature
  refine Finset.sum_bij (fun η _ => η) (by intro η _; simp)
    (fun _ _ _ _ h => h) (by intro η _; exact ⟨η,by simp,rfl⟩) ?_
  intro η _
  change factor (ofTypedColoredFinGraph (twoTerminalFinGraph G) label tag ut).code
    M U (mergeColor τ η) = _
  rw [ofTypedColoredFinGraph_factor]
  congr 1
  have hc (v : Bool ⊕ Fin p) :
      Sum.elim τ η ((Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) v) =
        TwoTerminal.extend (τ 0) (τ 1) η v := by
    rcases v with (v|v)
    · cases v <;> rfl
    · rfl
  apply Finset.prod_congr rfl
  intro i _
  exact congrArg₂ (M (label i)) (hc (G.src i)) (hc (G.dst i))

/-- Intrinsic unary labels interpret as exactly the prescribed-domain
indicators, with the original unary family left arbitrary. -/
theorem ofTypedColoredTwoTerminal_signature_domains (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ)
    (M : Fin bt → Matrix C C R) (U : Fin ut → C → R)
    (D : Fin dt → Set C) (τ : Fin 2 → C) :
    templateSignature (ofTypedColoredTwoTerminal G label tag ut) M
      (PrescribedDomains.extendedUnaries U D) τ =
      ∑ η : Fin p → C,
        (∏ j, PrescribedDomains.indicator (R:=R) (D (tag j)) (η j)) *
        ∏ i, M (label i) (TwoTerminal.extend (τ 0) (τ 1) η (G.src i))
          (TwoTerminal.extend (τ 0) (τ 1) η (G.dst i)) := by
  rw [ofTypedColoredTwoTerminal_signature]
  simp only [PrescribedDomains.extendedUnaries,Fin.addCases_right]

/-- When all used private labels have one common weight, the typed literal
signature agrees with the existing common-weight coloured signature. -/
theorem ofTypedColoredTwoTerminal_signature_common (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ)
    (M : Fin bt → Matrix C C R) (U : Fin (ut+dt) → C → R) (w : C → R)
    (hw : ∀ j, U (Fin.natAdd ut (tag j))=w) (τ : Fin 2 → C) :
    templateSignature (ofTypedColoredTwoTerminal G label tag ut) M U τ =
      TwoTerminal.coloredSignature G (fun i => M (label i)) w (τ 0) (τ 1) := by
  rw [ofTypedColoredTwoTerminal_signature]
  simp only [hw,TwoTerminal.coloredSignature]
  refine Finset.sum_bij (fun η _ => η) (by intro η _; simp)
    (fun _ _ _ _ h => h) (by intro η _; exact ⟨η,by simp,rfl⟩) ?_
  intro η _
  rfl

/-- The ordinary incidence graph retains the source gadget exactly. -/
def typedColoredEdgeTemplateIncidence (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ) :
    MultiGraph.IncidenceEquiv G
      ((ofTypedColoredTwoTerminal G label tag ut).edgeGadget rfl
        (ofTypedColoredTwoTerminal_valid G label tag ut)) :=
  ((G.reindexEquiv (Equiv.sumCongr finTwoEquiv.symm (Equiv.refl _)) (Equiv.refl _)).trans
    (ofTypedColoredFinGraphIncidenceEquiv (twoTerminalFinGraph G) label tag ut)).trans
      (((ofTypedColoredTwoTerminal G label tag ut).code.toMultiGraph
        (ofTypedColoredTwoTerminal_valid G label tag ut)).reindexEquiv
          ((ofTypedColoredTwoTerminal G label tag ut).terminalVertices rfl).symm (Equiv.refl _))

@[simp] theorem typedColoredEdgeTemplateIncidence_terminal
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e → Fin bt)
    (tag : Fin p → Fin dt) (ut : ℕ) (v : Bool) :
    (typedColoredEdgeTemplateIncidence G label tag ut).vertex (.inl v)=.inl v := by
  cases v <;> rfl

/-- Genuine outer-face planarity follows from the original gadget, independently
of its intrinsic metadata and source labels. -/
theorem ofTypedColoredTwoTerminal_planar (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e → Fin bt) (tag : Fin p → Fin dt) (ut : ℕ)
    (hG : TwoTerminal.PlanarEdgeGadget G) :
    TwoTerminal.PlanarEdgeGadget
      ((ofTypedColoredTwoTerminal G label tag ut).edgeGadget rfl
        (ofTypedColoredTwoTerminal_valid G label tag ut)) := by
  obtain ⟨d,hd⟩ := hG
  let i := typedColoredEdgeTemplateIncidence G label tag ut
  refine ⟨d.transport i,?_⟩
  have h := (d.outerCofacial_transport_iff i (.inl false) (.inl true)).mpr hd
  simpa only [i,typedColoredEdgeTemplateIncidence_terminal] using h

end PlanarHom.FixedGadgetNetwork
