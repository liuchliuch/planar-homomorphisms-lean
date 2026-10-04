import PlanarHom.PolygonalArc

/-! NEW path composition for rooted finite lane recursion. An incoming port is
either already local or carries an actual child path. Local ports are joined
without inserting a constant interval, so injectivity is preserved exactly. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph

/-- A local starting port or an actual path arriving from a child subtree. -/
inductive IncomingLane (x : Plane) where
  | localPort : IncomingLane x
  | child (y : Plane) (path : Path y x) : IncomingLane x

namespace IncomingLane
variable {x z : Plane}

def source : IncomingLane x → Plane
  | .localPort => x
  | .child y _ => y

def trace : IncomingLane x → Set Plane
  | .localPort => {x}
  | .child _ p => Set.range p

def Simple : IncomingLane x → Prop
  | .localPort => True
  | .child _ p => Function.Injective p

def join (p : IncomingLane x) (q : Path x z) : Path p.source z :=
  match p with
  | .localPort => q
  | .child _ p => p.trans q

theorem target_mem_trace (p : IncomingLane x) : x∈p.trace := by
  cases p with
  | localPort => exact Set.mem_singleton _
  | child y p => exact ⟨1,p.target⟩

theorem source_mem_trace (p : IncomingLane x) : p.source∈p.trace := by
  cases p with
  | localPort => exact Set.mem_singleton _
  | child y p => exact ⟨0,p.source⟩

theorem join_range (p : IncomingLane x) (q : Path x z) :
    Set.range (p.join q)=p.trace ∪ Set.range q := by
  cases p with
  | localPort =>
      change Set.range q={x} ∪ Set.range q
      have hx : x∈Set.range q := ⟨0,q.source⟩
      exact (Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hx)).symm
  | child y p => exact Path.trans_range p q

theorem join_injective (p : IncomingLane x) (q : Path x z) (hp : p.Simple)
    (hq : Function.Injective q) (hmeet : ∀ w∈p.trace, w∈Set.range q → w=x) :
    Function.Injective (p.join q) := by
  cases p with
  | localPort => exact hq
  | child y p => exact Polygonal.path_trans_injective p q hp hq hmeet

theorem joined_families_disjoint {A : Type*} {entry exit : A → Plane}
    (p : ∀ i, IncomingLane (entry i)) (q : ∀ i, Path (entry i) (exit i))
    (hp : ∀ i j, i≠j → Disjoint (p i).trace (p j).trace)
    (hq : ∀ i j, i≠j → Disjoint (Set.range (q i)) (Set.range (q j)))
    (hcross : ∀ i j, i≠j → Disjoint (p i).trace (Set.range (q j)))
    (i j : A) (hne : i≠j) :
    Disjoint (Set.range ((p i).join (q i))) (Set.range ((p j).join (q j))) := by
  rw [join_range,join_range]
  exact disjoint_union_left.mpr ⟨disjoint_union_right.mpr ⟨hp i j hne,hcross i j hne⟩,
    disjoint_union_right.mpr ⟨(hcross j i hne.symm).symm,hq i j hne⟩⟩

end IncomingLane
end PlanarHom.MultiGraph
