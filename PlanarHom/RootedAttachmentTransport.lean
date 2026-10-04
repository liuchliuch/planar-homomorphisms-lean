import PlanarHom.RootedReindex

/-! Root choice is an incidence reindexing; no input vertices are deleted. -/
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
local instance (priority := 10000) rootedAttachmentTransportDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V W E F J L : Type*}

def rootEquiv (r : V) : V ≃ PUnit ⊕ {v : V // v ≠ r} where
  toFun v := if h : v=r then .inl PUnit.unit else .inr ⟨v,h⟩
  invFun := Sum.elim (fun _ => r) Subtype.val
  left_inv v := by by_cases h : v=r <;> simp [h]
  right_inv a := by
    rcases a with (u|v)
    · cases u; simp
    · simp [v.property]

@[simp] theorem rootEquiv_root (r : V) : rootEquiv r r = .inl PUnit.unit := by simp [rootEquiv]
@[simp] theorem rootEquiv_symm_root (r : V) : (rootEquiv r).symm (.inl PUnit.unit) = r := rfl

def atRoot (G : MultiGraph V E) (r : V) : RootedGraph {v : V // v ≠ r} E :=
  G.reindex (rootEquiv r) (Equiv.refl E)

@[simp] theorem atRoot_planar_iff (G : MultiGraph V E) (r : V) : (G.atRoot r).Planar ↔ G.Planar :=
  planar_reindex_iff G _ _

def IncidenceEquiv.attachRooted {G : MultiGraph V E} {H : MultiGraph W F}
    (i : IncidenceEquiv G H) (K : RootedGraph J L) (r : V) :
    IncidenceEquiv (G.attachRooted K r) (H.attachRooted K (i.vertex r)) where
  vertex := Equiv.sumCongr i.vertex (Equiv.refl J)
  edge := Equiv.sumCongr i.edge (Equiv.refl L)
  src_eq e := by
    cases e with
    | inl e => simp [MultiGraph.attachRooted,i.src_eq]
    | inr e => cases he : K.src e <;> simp [MultiGraph.attachRooted,attachRootedVertex,he]
  dst_eq e := by
    cases e with
    | inl e => simp [MultiGraph.attachRooted,i.dst_eq]
    | inr e => cases he : K.dst e <;> simp [MultiGraph.attachRooted,attachRootedVertex,he]

def rootGlueEquiv (G : MultiGraph V E) (H : RootedGraph J L) (r : V) :
    IncidenceEquiv (RootedGraph.glue (G.atRoot r) H) (G.attachRooted H r) :=
  (RootedGraph.glueIncidenceEquiv (G.atRoot r) H).symm.trans
    ((G.reindexEquiv (rootEquiv r) (Equiv.refl E)).symm.attachRooted H (.inl PUnit.unit))

open scoped BigOperators
variable {C R : Type*} [Fintype V] [Fintype E] [Fintype J] [Fintype L] [Fintype C]
variable [CommSemiring R]

theorem partition_attachRooted (G : MultiGraph V E) (H : RootedGraph J L) (r : V)
    (M : Matrix C C R) (w : C → R) :
    (G.attachRooted H r).partition M w =
      ∑ i, w i * RootedGraph.signature (G.atRoot r) M w i * RootedGraph.signature H M w i := by
  rw [(rootGlueEquiv G H r).partition M w,RootedGraph.partition_glue]

end PlanarHom.MultiGraph
