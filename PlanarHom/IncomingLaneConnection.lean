import PlanarHom.OccurrenceKasteleynPortArrivals

/-! NEW direct connection of two rootward lanes by their original return arc.
Local endpoints are not padded by constant intervals, so simplicity survives. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.IncomingLane
variable {x y z : Plane}

def append (p : IncomingLane y) (q : Path x p.source) : Path x y :=
  match p with
  | .localPort => q
  | .child _ p => q.trans p

def prepend (p : IncomingLane x) (q : Path p.source y) : Path x y :=
  match p with
  | .localPort => q
  | .child _ p => p.symm.trans q

theorem append_range (p : IncomingLane y) (q : Path x p.source) :
    Set.range (p.append q)=Set.range q ∪ p.trace := by
  cases p with
  | localPort =>
      have hy : y∈Set.range q := ⟨1,q.target⟩
      exact (Set.union_eq_left.mpr (Set.singleton_subset_iff.mpr hy)).symm
  | child a p => exact Path.trans_range q p

theorem prepend_range (p : IncomingLane x) (q : Path p.source y) :
    Set.range (p.prepend q)=p.trace ∪ Set.range q := by
  cases p with
  | localPort =>
      have hx : x∈Set.range q := ⟨0,q.source⟩
      exact (Set.union_eq_right.mpr (Set.singleton_subset_iff.mpr hx)).symm
  | child a p =>
      change Set.range (p.symm.trans q)=_
      rw [Path.trans_range,Path.symm_range]
      rfl

theorem append_injective (p : IncomingLane y) (q : Path x p.source) (hp : p.Simple)
    (hq : Function.Injective q) (hmeet : ∀ w∈Set.range q, w∈p.trace → w=p.source) :
    Function.Injective (p.append q) := by
  cases p with
  | localPort => exact hq
  | child a p => exact Polygonal.path_trans_injective q p hq hp hmeet

theorem prepend_injective (p : IncomingLane x) (q : Path p.source y) (hp : p.Simple)
    (hq : Function.Injective q) (hmeet : ∀ w∈p.trace, w∈Set.range q → w=p.source) :
    Function.Injective (p.prepend q) := by
  cases p with
  | localPort => exact hq
  | child a p =>
      apply Polygonal.path_trans_injective p.symm q
        (hp.comp unitInterval.symm_bijective.injective) hq
      intro w hw hq
      rw [Path.symm_range] at hw
      exact hmeet w hw hq

def connect (p : IncomingLane x) (q : IncomingLane y) (middle : Path p.source q.source) : Path x y :=
  p.prepend (q.append middle)

theorem connect_range (p : IncomingLane x) (q : IncomingLane y) (middle : Path p.source q.source) :
    Set.range (p.connect q middle)=p.trace ∪ (Set.range middle ∪ q.trace) := by
  rw [connect,prepend_range,append_range]

theorem connect_injective (p : IncomingLane x) (q : IncomingLane y) (middle : Path p.source q.source)
    (hp : p.Simple) (hq : q.Simple) (hm : Function.Injective middle)
    (hpq : Disjoint p.trace q.trace)
    (hpm : ∀ w∈p.trace, w∈Set.range middle → w=p.source)
    (hmq : ∀ w∈Set.range middle, w∈q.trace → w=q.source) :
    Function.Injective (p.connect q middle) := by
  apply p.prepend_injective (q.append middle) hp (q.append_injective middle hq hm hmq)
  intro w hw hwq
  rw [q.append_range] at hwq
  rcases hwq with hwm | hwq
  · exact hpm w hw hwm
  · exact False.elim (Set.disjoint_left.mp hpq hw hwq)

end PlanarHom.MultiGraph.IncomingLane
