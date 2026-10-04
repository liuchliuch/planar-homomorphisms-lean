import PlanarHom.OccurrenceKasteleynPeelingMachines
import PlanarHom.MixedPlanarCode
import Mathlib.Data.List.NodupEquivFin

/-! NEW reconstruction. Literal deterministic depth-first traversal of an
ordinary mixed occurrence graph. Every edge position survives independently,
loops generate both incidences, and the program is total on malformed codes.
This file does not assert a planar embedding or solve an LR constraint system. -/
namespace PlanarHom.PlanarityDepthFirstSearch
open Complexity

abbrev Arc := ℕ × ℕ
abbrev Edge := ℕ × (ℕ × ℕ)

/-- Neighbour vertex and original occurrence index. A loop contributes twice. -/
def incidence (v : ℕ) (p : Edge × ℕ) : List Arc :=
  (if p.1.1 = v then [(p.1.2.1,p.2)] else []) ++
    (if p.1.2.1 = v then [(p.1.1,p.2)] else [])

def neighbours (g : MixedCode) (v : ℕ) : List Arc := g.edges.zipIdx.flatMap (incidence v)

structure Task where
  enter : Bool
  vertex : ℕ
  edge : ℕ
  path : List ℕ
  deriving DecidableEq, Repr

structure Discovery where
  vertex : ℕ
  treeEdge : ℕ
  ancestors : List ℕ
  deriving DecidableEq, Repr

structure State where
  work : List Task
  active : List ℕ
  discovered : List Discovery
  finished : List ℕ
  deriving DecidableEq, Repr

def seen (s : State) : List ℕ := s.discovered.map Discovery.vertex

def enterTask (v e : ℕ) (path : List ℕ) : Task := ⟨true,v,e,path⟩
def exitTask (v : ℕ) : Task := ⟨false,v,0,[]⟩

def childTasks (g : MixedCode) (v : ℕ) (path : List ℕ) : List Task :=
  (neighbours g v).map (fun a => enterTask a.1 a.2 path)

def step (g : MixedCode) (s : State) : State :=
  match s.work with
  | [] => s
  | t :: rest =>
    if t.enter then
      if t.vertex < g.vertices ∧ t.vertex ∉ seen s then
        ⟨childTasks g t.vertex (t.vertex::s.active) ++ exitTask t.vertex :: rest,
          t.vertex::s.active, ⟨t.vertex,t.edge,s.active⟩::s.discovered,s.finished⟩
      else ⟨rest,s.active,s.discovered,s.finished⟩
    else ⟨rest,s.active.tail,s.discovered,t.vertex::s.finished⟩

def initial (g : MixedCode) : State :=
  ⟨(List.range g.vertices).map (fun v => enterTask v g.edges.length []),[],[],[]⟩

/-- Enough fuel even with every vertex scanning the entire occurrence list. -/
def fuel (g : MixedCode) : ℕ := (g.vertices+1)*(2*g.edges.length+3)

def run (g : MixedCode) : State := (step g)^[fuel g] (initial g)

def discoveryOrder (g : MixedCode) : List ℕ := (run g).discovered.reverse.map Discovery.vertex

def finishOrder (g : MixedCode) : List ℕ := (run g).finished.reverse

def discoveryAt (g : MixedCode) (v : ℕ) : Discovery :=
  ((run g).discovered.find? (fun d => d.vertex == v)).getD ⟨v,g.edges.length,[]⟩

def ancestors (g : MixedCode) (v : ℕ) : List ℕ := (discoveryAt g v).ancestors

def parentEdge (g : MixedCode) (v : ℕ) : ℕ := (discoveryAt g v).treeEdge

def height (g : MixedCode) (v : ℕ) : ℕ := (ancestors g v).length

def parentVertex (g : MixedCode) (v : ℕ) : ℕ := (ancestors g v).headD g.vertices

 theorem incidence_length (v : ℕ) (p : Edge × ℕ) : (incidence v p).length ≤ 2 := by
  unfold incidence
  split_ifs <;> simp

 theorem neighbours_length (g : MixedCode) (v : ℕ) : (neighbours g v).length ≤ 2*g.edges.length := by
  unfold neighbours
  rw [List.length_flatMap]
  have hh := ListMapMachines.sum_map_le_mul (fun p => (incidence v p).length) g.edges.zipIdx 2
    (fun p hp => incidence_length v p)
  simpa [Nat.mul_comm] using hh

@[simp] theorem childTasks_length (g : MixedCode) (v : ℕ) (path : List ℕ) :
    (childTasks g v path).length = (neighbours g v).length := by simp [childTasks]

/-- Ordinary undirected adjacency remembers that some actual occurrence joins
these vertices; it does not merge occurrences in the executable program. -/
def Adjacent (g : MixedCode) (u v : ℕ) : Prop :=
  ∃ e ∈ g.edges, (e.1=u ∧ e.2.1=v) ∨ (e.1=v ∧ e.2.1=u)

 theorem adjacent_symm (g : MixedCode) {u v : ℕ} (h : Adjacent g u v) : Adjacent g v u := by
  obtain ⟨e,he,h⟩ := h
  exact ⟨e,he,h.symm⟩

 theorem mem_incidence (v : ℕ) (p : Edge × ℕ) (a : Arc) :
    a ∈ incidence v p ↔ (p.1.1=v ∧ a=(p.1.2.1,p.2)) ∨ (p.1.2.1=v ∧ a=(p.1.1,p.2)) := by
  unfold incidence
  split_ifs <;> simp_all

 theorem neighbours_adjacent (g : MixedCode) (v : ℕ) {a : Arc} (ha : a ∈ neighbours g v) :
    Adjacent g v a.1 := by
  obtain ⟨p,hp,ha⟩ := List.mem_flatMap.mp ha
  have he : p.1 ∈ g.edges := List.fst_mem_of_mem_zipIdx hp
  rcases (mem_incidence v p a).mp ha with ⟨hv,rfl⟩ | ⟨hv,rfl⟩
  · exact ⟨p.1,he,Or.inl ⟨hv,rfl⟩⟩
  · exact ⟨p.1,he,Or.inr ⟨rfl,hv⟩⟩

 theorem adjacent_neighbours (g : MixedCode) {u v : ℕ} (h : Adjacent g u v) :
    ∃ k, (v,k) ∈ neighbours g u := by
  obtain ⟨e,he,hor⟩ := h
  obtain ⟨i,hi,hei⟩ := List.mem_iff_getElem.mp he
  refine ⟨i,List.mem_flatMap.mpr ⟨(e,i),?_,?_⟩⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_some_iff.mpr ⟨hi,hei⟩)
  · rw [mem_incidence]
    rcases hor with ⟨hu,hv⟩ | ⟨hv,hu⟩
    · exact Or.inl ⟨hu,by simp [hv]⟩
    · exact Or.inr ⟨hu,by simp [hv]⟩

 theorem neighbours_vertex_valid (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (v : ℕ) {a : Arc} (ha : a ∈ neighbours g v) : a.1 < g.vertices := by
  obtain ⟨e,he,h⟩ := neighbours_adjacent g v ha
  have hv := hg.1 e he
  rcases h with ⟨h1,h2⟩ | ⟨h1,h2⟩ <;> omega

 theorem seen_step_mono (g : MixedCode) (s : State) : ∀ v ∈ seen s, v ∈ seen (step g s) := by
  unfold step
  split
  · exact fun v hv => hv
  · split_ifs <;> simp_all [seen]

 def GoodSeen (g : MixedCode) (s : State) : Prop :=
  (seen s).Nodup ∧ ∀ v ∈ seen s, v < g.vertices

 theorem goodSeen_initial (g : MixedCode) : GoodSeen g (initial g) := by simp [GoodSeen,seen,initial]

 theorem goodSeen_step (g : MixedCode) (s : State) (h : GoodSeen g s) : GoodSeen g (step g s) := by
  unfold step
  split
  · exact h
  · split_ifs <;> simp_all [GoodSeen,seen]

 theorem goodSeen_length (g : MixedCode) (s : State) (h : GoodSeen g s) :
    s.discovered.length ≤ g.vertices := by
  let xs : List (Fin g.vertices) := (seen s).attach.map (fun v => ⟨v.val,h.2 v.val v.property⟩)
  have hinj : Function.Injective (fun v : {v // v ∈ seen s} => (⟨v.val,h.2 v.val v.property⟩ : Fin g.vertices)) := by
    intro a b he
    exact Subtype.ext (congrArg Fin.val he)
  have hn : xs.Nodup := (List.nodup_attach.mpr h.1).map hinj
  have hh := hn.length_le_card
  simpa [xs,seen] using hh

end PlanarHom.PlanarityDepthFirstSearch
