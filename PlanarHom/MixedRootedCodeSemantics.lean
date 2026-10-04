import PlanarHom.MixedRootedCodeMachines
import PlanarHom.MixedInstanceCodeSemantics
import PlanarHom.MixedRootedAttachment
import PlanarHom.RootedCodeSemantics

noncomputable section
open Classical
namespace PlanarHom.MixedRootedCodeMachines
open Complexity Complexity.MixedCode
variable {n m k b u:ℕ}

@[simp] theorem attach_edges_length (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) :
    (attach H p).edges.length=p.2.edges.length+m := by simp [attach,newEdges]
@[simp] theorem attach_unaries_length (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) :
    (attach H p).unaries.length=p.2.unaries.length+k := by simp [attach,newUnaries]

theorem attach_valid (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode)
    (hg:p.2.Valid b u) (hr:p.1<p.2.vertices) : (attach H p).Valid b u := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · have h:=hg.1 e he
      exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2.1.trans_le (Nat.le_add_right _ _),h.2.2⟩
    · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp he
      exact ⟨RootedCodeMachines.endpoint_lt _ _ hr _,RootedCodeMachines.endpoint_lt _ _ hr _,(H.edgeLabel i).isLt⟩
  · intro f hf
    rcases List.mem_append.mp hf with hf|hf
    · have h:=hg.2 f hf
      exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2⟩
    · obtain ⟨i,rfl⟩:=List.mem_ofFn.mp hf
      exact ⟨RootedCodeMachines.endpoint_lt _ _ hr _,(H.unaryLabel i).isLt⟩

def edgeEquiv (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) :
    Fin p.2.edges.length⊕Fin m ≃ Fin (attach H p).edges.length :=
  finSumFinEquiv.trans (finCongr (attach_edges_length H p).symm)

def unaryEquiv (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) :
    Fin p.2.unaries.length⊕Fin k ≃ Fin (attach H p).unaries.length :=
  finSumFinEquiv.trans (finCongr (attach_unaries_length H p).symm)

theorem get_old_edge (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) (e:Fin p.2.edges.length) :
    (attach H p).edges.get (edgeEquiv H p (.inl e))=p.2.edges.get e := by
  simp [edgeEquiv,attach,List.get_eq_getElem]

theorem get_new_edge (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) (e:Fin m) :
    (attach H p).edges.get (edgeEquiv H p (.inr e))=
      (RootedCodeMachines.endpoint p.2.vertices p.1 (H.graph.src e),
       RootedCodeMachines.endpoint p.2.vertices p.1 (H.graph.dst e),(H.edgeLabel e).val) := by
  simp [edgeEquiv,attach,newEdges,List.get_eq_getElem]

theorem get_old_unary (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) (f:Fin p.2.unaries.length) :
    (attach H p).unaries.get (unaryEquiv H p (.inl f))=p.2.unaries.get f := by
  simp [unaryEquiv,attach,List.get_eq_getElem]

theorem get_new_unary (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (p:ℕ×MixedCode) (f:Fin k) :
    (attach H p).unaries.get (unaryEquiv H p (.inr f))=
      (RootedCodeMachines.endpoint p.2.vertices p.1 (H.unaryHost f),(H.unaryLabel f).val) := by
  simp [unaryEquiv,attach,newUnaries,List.get_eq_getElem]

/-- Exact incidence and label correspondence for every original and added
binary/unary occurrence, including repeated root unaries and loops. -/
def instanceEquivalence (H:MixedRooted (Fin n) (Fin m) (Fin k) b u)
    (g:MixedCode) (hg:g.Valid b u) (r:Fin g.vertices) :
    MixedInstance.Equivalence ((g.toMixedInstance hg).attach H r)
      ((attach H (r.val,g)).toMixedInstance (attach_valid H _ hg r.isLt)) where
  vertex:=finSumFinEquiv
  edge:=edgeEquiv H (r.val,g)
  unary:=unaryEquiv H (r.val,g)
  src_eq e:=by
    cases e with
    | inl e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inl e))).1=_
      rw [get_old_edge]
      rfl
    | inr e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inr e))).1=_
      rw [get_new_edge]
      exact RootedCodeMachines.endpoint_equiv g r (H.graph.src e)
  dst_eq e:=by
    cases e with
    | inl e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inl e))).2.1=_
      rw [get_old_edge]
      rfl
    | inr e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inr e))).2.1=_
      rw [get_new_edge]
      exact RootedCodeMachines.endpoint_equiv g r (H.graph.dst e)
  edgeLabel_eq e:=by
    cases e with
    | inl e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inl e))).2.2=_
      rw [get_old_edge]
      rfl
    | inr e=>
      apply Fin.ext
      change ((attach H (r.val,g)).edges.get (edgeEquiv H _ (.inr e))).2.2=_
      rw [get_new_edge]
      rfl
  unaryHost_eq f:=by
    cases f with
    | inl f=>
      apply Fin.ext
      change ((attach H (r.val,g)).unaries.get (unaryEquiv H _ (.inl f))).1=_
      rw [get_old_unary]
      rfl
    | inr f=>
      apply Fin.ext
      change ((attach H (r.val,g)).unaries.get (unaryEquiv H _ (.inr f))).1=_
      rw [get_new_unary]
      exact RootedCodeMachines.endpoint_equiv g r (H.unaryHost f)
  unaryLabel_eq f:=by
    cases f with
    | inl f=>
      apply Fin.ext
      change ((attach H (r.val,g)).unaries.get (unaryEquiv H _ (.inl f))).2=_
      rw [get_old_unary]
      rfl
    | inr f=>
      apply Fin.ext
      change ((attach H (r.val,g)).unaries.get (unaryEquiv H _ (.inr f))).2=_
      rw [get_new_unary]
      rfl

theorem attach_planarValid (H:MixedRooted (Fin n) (Fin m) (Fin k) b u) (hH:H.graph.Planar)
    (g:MixedCode) (hg:g.PlanarValid b u) (r:Fin g.vertices) :
    (attach H (r.val,g)).PlanarValid b u := by
  rw [MixedCode.planarValid_iff _ (attach_valid H _ hg.1 r.isLt)]
  let e:=instanceEquivalence H g hg.1 r
  let i:MultiGraph.IncidenceEquiv (((g.toMixedInstance hg.1).attach H r).graph)
      (((attach H (r.val,g)).toMixedInstance (attach_valid H _ hg.1 r.isLt)).graph):=
    ⟨e.vertex,e.edge,e.src_eq,e.dst_eq⟩
  apply i.planar_iff.mp
  exact ((MixedCode.planarValid_iff g hg.1).mp hg).attachRooted hH r

variable {C K:Type} [Fintype C] [Field K]

theorem evaluate_attach (H:MixedRooted (Fin n) (Fin m) (Fin k) b u)
    (g:MixedCode) (hg:g.Valid b u) (r:Fin g.vertices) (M:Fin b→Matrix C C K)
    (U:Fin u→C→K) (w:C→K) :
    (attach H (r.val,g)).evaluate (attach_valid H _ hg r.isLt) M U w=
      ((g.toMixedInstance hg).attach H r).partition M U w := by
  rw [evaluate_toMixedInstance]
  exact (instanceEquivalence H g hg r).partition M U w

end PlanarHom.MixedRootedCodeMachines
