import PlanarHom.RootedGadgets

/-! Attach a rooted occurrence graph at an arbitrary vertex of a host graph. -/
namespace PlanarHom.MultiGraph
variable {V W E F : Type*}

def attachRootedVertex (r : V) : PUnit ⊕ W → V ⊕ W :=
  Sum.elim (fun _ => .inl r) Sum.inr

/-- Only the distinguished root is identified; all other vertices and every
old/new edge occurrence are retained. -/
def attachRooted (G : MultiGraph V E) (H : RootedGraph W F) (r : V) :
    MultiGraph (V ⊕ W) (E ⊕ F) where
  src := Sum.elim (fun e => .inl (G.src e)) (fun f => attachRootedVertex r (H.src f))
  dst := Sum.elim (fun e => .inl (G.dst e)) (fun f => attachRootedVertex r (H.dst f))

end PlanarHom.MultiGraph
