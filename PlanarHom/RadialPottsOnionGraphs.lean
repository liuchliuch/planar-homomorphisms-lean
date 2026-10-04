import PlanarHom.RadialPottsOnionBoundaryAtlasEdges
import PlanarHom.PottsRandomCluster
import PlanarHom.PlanarTransport

/-! NEW reconstruction: literal red onion and incidence connectivity transport.
These definitions support the surviving exact quarter-turn proof. -/
noncomputable section
open Classical
namespace PlanarHom.PottsCentered
open MultiGraph
variable {V E W F : Type} [Fintype E] [Fintype F]

theorem component_relation_incidenceEquiv {G : MultiGraph V E} {H : MultiGraph W F}
    (i : G.IncidenceEquiv H) {u v : V} (h : G.componentSetoid Finset.univ u v) :
    H.componentSetoid Finset.univ (i.vertex u) (i.vertex v) := by
  induction h with
  | rel u v h =>
    obtain ⟨e,_,rfl,rfl⟩ := h
    exact Relation.EqvGen.rel _ _ ⟨i.edge e,Finset.mem_univ _,i.src_eq e,i.dst_eq e⟩
  | refl => exact Relation.EqvGen.refl _
  | symm _ _ _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans _ _ _ _ _ ih ij => exact Relation.EqvGen.trans _ _ _ ih ij
end PlanarHom.PottsCentered

namespace PlanarHom.RadialPottsTile.OnionBoundary
open MultiGraph

def withShort {k : ℕ} (a b : HalfShort k → White k) :
    MultiGraph (Vertex k) (Long k ⊕ HalfShort k) where
  src := Sum.elim (fun e => .inl (longLeft e)) (fun e => .inl (a e))
  dst := Sum.elim longRight (fun e => .inl (b e))

def redGraph (k : ℕ) := withShort (@evenWhite k) (@oddWhite k)
def switchedRedGraph (k : ℕ) := withShort (switch ∘ @evenWhite k) (switch ∘ @oddWhite k)
end PlanarHom.RadialPottsTile.OnionBoundary
