import PlanarHom.RootedCodeMachines
import PlanarHom.MixedPlanarCode
import PlanarHom.RootedPlanarity

/-! Exact incidence of the compiled rooted-gadget attachment. -/
noncomputable section
open Classical
namespace PlanarHom.RootedCodeMachines
open Complexity Complexity.MixedCode
variable {n m bt ut : ℕ}

@[simp] theorem attach_vertices (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) :
    (attach H selected p).vertices = p.2.vertices+n := rfl
@[simp] theorem attach_edges_length (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) :
    (attach H selected p).edges.length = p.2.edges.length+m := by simp [attach,newEdges]
@[simp] theorem attach_unaries (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) :
    (attach H selected p).unaries = p.2.unaries := rfl

theorem endpoint_lt (vertices root : ℕ) (hr : root < vertices) (a : PUnit ⊕ Fin n) :
    endpoint vertices root a < vertices+n := by
  cases a with
  | inl u => dsimp [endpoint]; omega
  | inr v => dsimp [endpoint]; omega

theorem attach_valid (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode)
    (hg : p.2.Valid bt ut) (hr : p.1 < p.2.vertices) (hs : selected < bt) :
    (attach H selected p).Valid bt ut := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · have h := hg.1 e he
      exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2.1.trans_le (Nat.le_add_right _ _),h.2.2⟩
    · obtain ⟨i,rfl⟩ := List.mem_ofFn.mp he
      exact ⟨endpoint_lt _ _ hr _,endpoint_lt _ _ hr _,hs⟩
  · intro u hu
    have h := hg.2 u hu
    exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2⟩

def attachEdgeEquiv (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode) :
    Fin p.2.edges.length ⊕ Fin m ≃ Fin (attach H selected p).edges.length :=
  finSumFinEquiv.trans (finCongr (attach_edges_length H selected p).symm)

theorem attach_get_old (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode)
    (e : Fin p.2.edges.length) :
    (attach H selected p).edges.get (attachEdgeEquiv H selected p (.inl e)) = p.2.edges.get e := by
  simp [attachEdgeEquiv,attach,List.get_eq_getElem]

theorem attach_get_new (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (p : ℕ × MixedCode)
    (e : Fin m) :
    (attach H selected p).edges.get (attachEdgeEquiv H selected p (.inr e)) =
      (endpoint p.2.vertices p.1 (H.src e),endpoint p.2.vertices p.1 (H.dst e),selected) := by
  simp [attachEdgeEquiv,attach,newEdges,List.get_eq_getElem]

theorem endpoint_equiv (g : MixedCode) (r : Fin g.vertices) (a : PUnit ⊕ Fin n) :
    endpoint g.vertices r.val a =
      (finSumFinEquiv (MultiGraph.attachRootedVertex r a)).val := by
  cases a <;> rfl

/-- Both endpoints of each old/new occurrence are preserved, including loops. -/
def attachIncidenceEquiv (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (g : MixedCode)
    (hg : g.Valid bt ut) (r : Fin g.vertices) (hs : selected < bt) :
    MultiGraph.IncidenceEquiv ((g.toMultiGraph hg).attachRooted H r)
      ((attach H selected (r.val,g)).toMultiGraph (attach_valid H selected _ hg r.isLt hs)) where
  vertex := finSumFinEquiv
  edge := attachEdgeEquiv H selected (r.val,g)
  src_eq e := by
    cases e with
    | inl e =>
      apply Fin.ext
      change ((attach H selected (r.val,g)).edges.get (attachEdgeEquiv H selected _ (.inl e))).1 = _
      rw [attach_get_old]
      rfl
    | inr e =>
      apply Fin.ext
      change ((attach H selected (r.val,g)).edges.get (attachEdgeEquiv H selected _ (.inr e))).1 = _
      rw [attach_get_new]
      exact endpoint_equiv g r (H.src e)
  dst_eq e := by
    cases e with
    | inl e =>
      apply Fin.ext
      change ((attach H selected (r.val,g)).edges.get (attachEdgeEquiv H selected _ (.inl e))).2.1 = _
      rw [attach_get_old]
      rfl
    | inr e =>
      apply Fin.ext
      change ((attach H selected (r.val,g)).edges.get (attachEdgeEquiv H selected _ (.inr e))).2.1 = _
      rw [attach_get_new]
      exact endpoint_equiv g r (H.dst e)

/-- Every compiled attachment query is ordinarily planar. The root need not be
on a supplied outer face; the geometric theorem chooses the needed drawing. -/
theorem attach_planarValid (H : RootedGraph (Fin n) (Fin m)) (hH : H.Planar)
    (selected : ℕ) (g : MixedCode) (hg : g.PlanarValid bt ut)
    (r : Fin g.vertices) (hs : selected < bt) :
    (attach H selected (r.val,g)).PlanarValid bt ut := by
  rw [MixedCode.planarValid_iff _ (attach_valid H selected _ hg.1 r.isLt hs)]
  apply (attachIncidenceEquiv H selected g hg.1 r hs).planar_iff.mp
  exact ((MixedCode.planarValid_iff g hg.1).mp hg).attachRooted hH r

end PlanarHom.RootedCodeMachines
