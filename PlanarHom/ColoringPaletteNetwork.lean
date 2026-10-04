import PlanarHom.ColoringClausePaletteState

/-! The literal global palette graph: actual clause patches share only their
primary variable vertices; exclusive diamonds synchronize selected sector pairs.
No component is silently normalized. The theorem below is independent of the
later geometric choice of a cyclic palette-link network. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringPaletteNetwork
open MultiGraph PlanarColoringClause ThreeColorPaletteCounting
set_option maxHeartbeats 6000000
set_option maxRecDepth 8000

variable {V C L : Type}
abbrev Sector := C × Fin 3
abbrev Vertex (V C L : Type) := V ⊕ ((C × Fin 3 × Bool) ⊕ ((C × InternalVertex) ⊕ L))
abbrev Edge (C L : Type) := (C × PlanarColoringClause.Edge) ⊕ (L × Fin 6)

variable (occurrence : C → Fin 3 → V) (left right : L → Sector (C := C))

def black (c : C) (k : Fin 3) : Vertex V C L := .inr (.inl (c,k,false))
def gray (c : C) (k : Fin 3) : Vertex V C L := .inr (.inl (c,k,true))
def center (l : L) : Vertex V C L := .inr (.inr (.inr l))
def clauseInternal (c : C) (v : InternalVertex) : Vertex V C L := .inr (.inr (.inl (c,v)))

def portMap (c : C) : Fin 9 → Vertex V C L :=
  ![.inl (occurrence c 0),black c 0,gray c 0,
    .inl (occurrence c 1),black c 1,gray c 1,
    .inl (occurrence c 2),black c 2,gray c 2]

def clauseMap (c : C) : Fin 9 ⊕ InternalVertex → Vertex V C L :=
  Sum.elim (portMap occurrence c) (clauseInternal c)

@[simp] theorem clauseMap_primary (c : C) (k : Fin 3) :
    clauseMap occurrence c (.inl (primaryPort k))=(.inl (occurrence c k) : Vertex V C L) := by
  fin_cases k <;> rfl
@[simp] theorem clauseMap_black (c : C) (k : Fin 3) :
    clauseMap occurrence c (.inl (blackPort k))=(black c k : Vertex V C L) := by
  fin_cases k <;> rfl
@[simp] theorem clauseMap_gray (c : C) (k : Fin 3) :
    clauseMap occurrence c (.inl (grayPort k))=(gray c k : Vertex V C L) := by
  fin_cases k <;> rfl

def wheelMap (l : L) : Fin 5 → Vertex V C L :=
  ![black (left l).1 (left l).2,gray (left l).1 (left l).2,
    black (right l).1 (right l).2,gray (right l).1 (right l).2,center l]

/-- The two palette rim edges already belong to the clause patches. Reusing
them avoids parallel copies of an identical geometric segment. -/
def wheelEdge : Fin 6 → Fin 8 := ![1,3,4,5,6,7]

def graph : MultiGraph (Vertex V C L) (Edge C L) where
  src := Sum.elim (fun p => clauseMap occurrence p.1 (patchGraph.src p.2))
    (fun p => wheelMap left right p.1 (PlanarColoringExclusiveCrossing.graph.src (wheelEdge p.2)))
  dst := Sum.elim (fun p => clauseMap occurrence p.1 (patchGraph.dst p.2))
    (fun p => wheelMap left right p.1 (PlanarColoringExclusiveCrossing.graph.dst (wheelEdge p.2)))

def Proper (col : Vertex V C L → Fin 3) : Prop :=
  ∀ e,col ((graph occurrence left right).src e)≠col ((graph occurrence left right).dst e)

theorem clause_proper (col : Vertex V C L → Fin 3) (h : Proper occurrence left right col) (c : C) :
    PatchProper (col ∘ clauseMap occurrence c) := fun e => h (.inl (c,e))

theorem palette_separated (col : Vertex V C L → Fin 3)
    (h : Proper occurrence left right col) (c : C) (k : Fin 3) : col (black c k)≠col (gray c k) := by
  obtain ⟨s,hs⟩ := exists_state (col ∘ clauseMap occurrence c) (clause_proper occurrence left right col h c)
  have hb := congrFun hs (.inl (blackPort k))
  have hg := congrFun hs (.inl (grayPort k))
  simp only [Function.comp_apply,clauseMap_black,clauseMap_gray,stateExtension_port,
    statePort_black,statePort_gray] at hb hg
  rw [hb,hg]
  exact s.1.property

theorem proper_split (col : Vertex V C L → Fin 3) : Proper occurrence left right col ↔
    (∀ c,PatchProper (col ∘ clauseMap occurrence c)) ∧
      ∀ l,PlanarColoringExclusiveCrossing.Proper (col ∘ wheelMap left right l) := by
  constructor
  · intro h
    refine ⟨clause_proper occurrence left right col h,?_⟩
    intro l e
    fin_cases e
    · exact palette_separated occurrence left right col h (left l).1 (left l).2
    · exact h (.inr (l,0))
    · exact palette_separated occurrence left right col h (right l).1 (right l).2
    · exact h (.inr (l,1))
    · exact h (.inr (l,2))
    · exact h (.inr (l,3))
    · exact h (.inr (l,4))
    · exact h (.inr (l,5))
  · rintro ⟨hc,hl⟩ (⟨c,e⟩ | ⟨l,e⟩)
    · exact hc c e
    · exact hl l (wheelEdge e)

def Shared (s : C → PaletteState) : Prop :=
  ∀ c d k j,occurrence c k=occurrence d j →
    statePort (s c) (primaryPort k)=statePort (s d) (primaryPort j)

def Linked (s : C → PaletteState) : Prop := ∀ l,(s (left l).1).1=(s (right l).1).1

abbrev State := {s : C → PaletteState // Shared occurrence s ∧ Linked left right s}

variable (cover : ∀ v,∃ c k,occurrence c k=v)

def owner (v : V) : C := (cover v).choose
def slot (v : V) : Fin 3 := ((cover v).choose_spec).choose

theorem owner_slot (v : V) : occurrence (owner occurrence cover v) (slot occurrence cover v)=v :=
  ((cover v).choose_spec).choose_spec

def realize (s : C → PaletteState) : Vertex V C L → Fin 3
  | .inl v => statePort (s (owner occurrence cover v)) (primaryPort (slot occurrence cover v))
  | .inr (.inl (c,k,false)) => (s c).1.val.1
  | .inr (.inl (c,k,true)) => (s c).1.val.2
  | .inr (.inr (.inl (c,v))) => stateExtension (s c) (.inr v)
  | .inr (.inr (.inr l)) => PlanarColoringExclusiveCrossing.third
      (s (left l).1).1.val.1 (s (left l).1).1.val.2

@[simp] theorem realize_primary (s : C → PaletteState) (hs : Shared occurrence s) (c : C) (k : Fin 3) :
    realize occurrence left cover s (.inl (occurrence c k))=statePort (s c) (primaryPort k) := by
  exact hs _ _ _ _ (owner_slot occurrence cover (occurrence c k))

theorem realize_clause (s : C → PaletteState) (hs : Shared occurrence s) (c : C) :
    realize occurrence left cover s ∘ clauseMap occurrence c=stateExtension (s c) := by
  funext v
  cases v with
  | inl k =>
    fin_cases k
    all_goals first
      | exact realize_primary occurrence left cover s hs c 0
      | exact realize_primary occurrence left cover s hs c 1
      | exact realize_primary occurrence left cover s hs c 2
      | rfl
  | inr v => rfl

theorem realize_wheel (s : C → PaletteState) (hs : Linked left right s) (l : L) :
    realize occurrence left cover s ∘ wheelMap left right l=
      PlanarColoringExclusiveCrossing.extension (s (left l).1).1.val.1 (s (left l).1).1.val.2 := by
  funext k
  have he := hs l
  fin_cases k
  · rfl
  · rfl
  · exact congrArg (fun p : Palette => p.val.1) he.symm
  · exact congrArg (fun p : Palette => p.val.2) he.symm
  · rfl

theorem realize_proper (s : State occurrence left right) : Proper occurrence left right (realize occurrence left cover s.val) := by
  rw [proper_split]
  constructor
  · intro c
    rw [realize_clause occurrence left cover s.val s.property.1]
    exact stateExtension_proper (s.val c)
  · intro l
    rw [realize_wheel occurrence left right cover s.val s.property.2]
    exact PlanarColoringExclusiveCrossing.extension_proper _ _ (s.val (left l).1).1.property

/-- Proper global colorings recover one uniquely determined state per actual
clause, and every exclusive diamond enforces equality of its two palettes. -/
theorem state_of_proper (col : Vertex V C L → Fin 3) (hp : Proper occurrence left right col) :
    ∃ s : State occurrence left right,∀ c,col ∘ clauseMap occurrence c=stateExtension (s.val c) := by
  have hex : ∀ c,∃ s : PaletteState,col ∘ clauseMap occurrence c=stateExtension s :=
    fun c => exists_state _ (clause_proper occurrence left right col hp c)
  choose s hs using hex
  have hblack (c : C) (k : Fin 3) : col (black c k)=(s c).1.val.1 := by
    have h := congrFun (hs c) (.inl (blackPort k))
    simpa only [Function.comp_apply,clauseMap_black,stateExtension_port,statePort_black] using h
  have hgray (c : C) (k : Fin 3) : col (gray c k)=(s c).1.val.2 := by
    have h := congrFun (hs c) (.inl (grayPort k))
    simpa only [Function.comp_apply,clauseMap_gray,stateExtension_port,statePort_gray] using h
  refine ⟨⟨s,?_,?_⟩,hs⟩
  · intro c d k j he
    have hc := congrFun (hs c) (.inl (primaryPort k))
    have hd := congrFun (hs d) (.inl (primaryPort j))
    simp only [Function.comp_apply,clauseMap_primary,stateExtension_port] at hc hd
    exact hc.symm.trans ((congrArg (fun v => col (.inl v)) he).trans hd)
  · intro l
    have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp
      (((proper_split occurrence left right col).mp hp).2 l)
    have hb := congrFun hw.2 2
    have hg := congrFun hw.2 3
    change col (black (right l).1 (right l).2)=col (black (left l).1 (left l).2) at hb
    change col (gray (right l).1 (right l).2)=col (gray (left l).1 (left l).2) at hg
    apply Subtype.ext
    exact Prod.ext (by simpa only [hblack] using hb.symm) (by simpa only [hgray] using hg.symm)

theorem reconstruct (col : Vertex V C L → Fin 3) (hp : Proper occurrence left right col)
    (s : C → PaletteState) (hs : ∀ c,col ∘ clauseMap occurrence c=stateExtension (s c)) :
    col=realize occurrence left cover s := by
  have hblack (c : C) (k : Fin 3) : col (black c k)=(s c).1.val.1 := by
    have h := congrFun (hs c) (.inl (blackPort k))
    simpa only [Function.comp_apply,clauseMap_black,stateExtension_port,statePort_black] using h
  have hgray (c : C) (k : Fin 3) : col (gray c k)=(s c).1.val.2 := by
    have h := congrFun (hs c) (.inl (grayPort k))
    simpa only [Function.comp_apply,clauseMap_gray,stateExtension_port,statePort_gray] using h
  funext v
  rcases v with v | (⟨c,k,b⟩ | (⟨c,w⟩ | l))
  · have h := congrFun (hs (owner occurrence cover v)) (.inl (primaryPort (slot occurrence cover v)))
    simpa only [Function.comp_apply,clauseMap_primary,owner_slot,stateExtension_port,realize] using h
  · cases b
    · exact hblack c k
    · exact hgray c k
  · exact congrFun (hs c) (.inr w)
  · have hw := (PlanarColoringExclusiveCrossing.proper_iff _).mp
      (((proper_split occurrence left right col).mp hp).2 l)
    have h := congrFun hw.2 4
    change col (center l)=PlanarColoringExclusiveCrossing.third
      (col (black (left l).1 (left l).2)) (col (gray (left l).1 (left l).2)) at h
    simpa only [hblack,hgray] using h

/-- A genuine bijection for the materialized global graph. This retains the
independent palettes of disconnected clause components. -/
def coloringStateEquiv : Coloring (graph occurrence left right) ≃ State occurrence left right :=
  (Equiv.ofBijective
    (fun s : State occurrence left right =>
      (⟨realize occurrence left cover s.val,realize_proper occurrence left right cover s⟩ :
        Coloring (graph occurrence left right)))
    ⟨by
      intro s t h
      apply Subtype.ext
      funext c
      apply stateExtension_injective
      have hh := congrArg (fun f : Coloring (graph occurrence left right) =>
        f.val ∘ clauseMap occurrence c) h
      simpa only [realize_clause occurrence left cover s.val s.property.1,
        realize_clause occurrence left cover t.val t.property.1] using hh,
     by
      intro col
      obtain ⟨s,hs⟩ := state_of_proper occurrence left right col.val col.property
      exact ⟨s,Subtype.ext (reconstruct occurrence left right cover col.val col.property s.val hs).symm⟩⟩).symm

include cover in
theorem coloring_card [Fintype V] [Fintype C] [Fintype L] :
    ProperColoringPottsReduction.properColoringCount (graph occurrence left right) 3=
      Nat.card (State occurrence left right) := by
  rw [properCount_eq_natCard]
  exact Nat.card_congr (coloringStateEquiv occurrence left right cover)

end PlanarHom.ColoringPaletteNetwork
