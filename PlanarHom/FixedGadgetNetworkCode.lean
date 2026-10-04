import PlanarHom.MixedPlanarCode

/-! Newly reimplemented literal fixed-template network syntax and compiler.
Every gate is an occurrence, not a set member. Only private vertices are added;
all pre-existing vertices, edges and unary occurrences are retained verbatim. -/
namespace PlanarHom.FixedGadgetNetwork
open Complexity

structure Template where
  boundary : ℕ
  privateCount : ℕ
  edges : List (ℕ × ℕ × ℕ)
  unaries : List (ℕ × ℕ)
  deriving DecidableEq

def Template.code (t : Template) : MixedCode :=
  ⟨t.boundary+t.privateCount,t.edges,t.unaries⟩

def emptyTemplate : Template := ⟨0,0,[],[]⟩

abbrev Gate := ℕ × List ℕ

def gateTemplate (ts : List Template) (a : Gate) : Template := ts.getD a.1 emptyTemplate

def Gate.Valid (ts : List Template) (shared : ℕ) (a : Gate) : Prop :=
  a.1<ts.length ∧ a.2.length=(gateTemplate ts a).boundary ∧ ∀v∈a.2,v<shared

structure Network where
  base : MixedCode
  gates : List Gate
  deriving DecidableEq

def Network.Valid (ts : List Template) (bt ut : ℕ) (n : Network) : Prop :=
  n.base.Valid bt ut ∧ (∀t∈ts,t.code.Valid bt ut) ∧ ∀a∈n.gates,a.Valid ts n.base.vertices

def remapVertex (t : Template) (offset : ℕ) (ports : List ℕ) (v : ℕ) : ℕ :=
  if v<t.boundary then ports.getD v 0 else offset+(v-t.boundary)

def remapEdge (t : Template) (offset : ℕ) (ports : List ℕ) (e : ℕ × ℕ × ℕ) : ℕ × ℕ × ℕ :=
  (remapVertex t offset ports e.1,remapVertex t offset ports e.2.1,e.2.2)

def remapUnary (t : Template) (offset : ℕ) (ports : List ℕ) (u : ℕ × ℕ) : ℕ × ℕ :=
  (remapVertex t offset ports u.1,u.2)

def attachTemplate (t : Template) (g : MixedCode) (ports : List ℕ) : MixedCode :=
  ⟨g.vertices+t.privateCount,
   g.edges ++ t.edges.map (remapEdge t g.vertices ports),
   g.unaries ++ t.unaries.map (remapUnary t g.vertices ports)⟩

def compileStep (ts : List Template) (g : MixedCode) (a : Gate) : MixedCode :=
  attachTemplate (gateTemplate ts a) g a.2

def compile (ts : List Template) (n : Network) : MixedCode :=
  n.gates.foldl (compileStep ts) n.base

theorem remapVertex_lt (t : Template) (offset : ℕ) (ports : List ℕ)
    (hp : ports.length=t.boundary) (hr : ∀v∈ports,v<offset)
    (v : ℕ) (hv : v<t.boundary+t.privateCount) :
    remapVertex t offset ports v<offset+t.privateCount := by
  unfold remapVertex
  split_ifs with h
  · have hi : v<ports.length := by omega
    have hm : ports.getD v 0∈ports := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
    exact (hr _ hm).trans_le (Nat.le_add_right _ _)
  · omega

theorem attachTemplate_valid (t : Template) (g : MixedCode) (ports : List ℕ)
    {bt ut : ℕ} (ht : t.code.Valid bt ut) (hg : g.Valid bt ut)
    (hp : ports.length=t.boundary) (hr : ∀v∈ports,v<g.vertices) :
    (attachTemplate t g ports).Valid bt ut := by
  constructor
  · intro e he
    rcases List.mem_append.mp he with he|he
    · have h := hg.1 e he
      exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2.1.trans_le (Nat.le_add_right _ _),h.2.2⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp he
      have h := ht.1 a ha
      exact ⟨remapVertex_lt t g.vertices ports hp hr a.1 h.1,
        remapVertex_lt t g.vertices ports hp hr a.2.1 h.2.1,h.2.2⟩
  · intro u hu
    rcases List.mem_append.mp hu with hu|hu
    · have h := hg.2 u hu
      exact ⟨h.1.trans_le (Nat.le_add_right _ _),h.2⟩
    · obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hu
      have h := ht.2 a ha
      exact ⟨remapVertex_lt t g.vertices ports hp hr a.1 h.1,h.2⟩

theorem gateTemplate_mem {ts : List Template} {a : Gate} (h : a.1<ts.length) :
    gateTemplate ts a∈ts := by
  rw [gateTemplate,List.getD_eq_getElem _ _ h]
  exact List.getElem_mem h

theorem compile_valid (ts : List Template) {bt ut shared : ℕ}
    (ht : ∀t∈ts,t.code.Valid bt ut) (g : MixedCode) (as : List Gate)
    (hg : g.Valid bt ut) (hs : shared≤g.vertices)
    (ha : ∀a∈as,a.Valid ts shared) : (compile ts ⟨g,as⟩).Valid bt ut := by
  induction as generalizing g with
  | nil => exact hg
  | cons a as ih =>
    have hv := ha a (by simp)
    exact ih (compileStep ts g a)
      (attachTemplate_valid _ _ _ (ht _ (gateTemplate_mem hv.1)) hg hv.2.1
        (fun v hm=>(hv.2.2 v hm).trans_le hs))
      (hs.trans (Nat.le_add_right _ _)) (fun b hb=>ha b (by simp [hb]))

@[simp] theorem compile_vertices (ts : List Template) (g : MixedCode) (as : List Gate) :
    (compile ts ⟨g,as⟩).vertices=g.vertices+(as.map (fun a=>(gateTemplate ts a).privateCount)).sum := by
  induction as generalizing g with
  | nil => simp [compile]
  | cons a as ih =>
    change (compile ts ⟨compileStep ts g a,as⟩).vertices=_
    rw [ih]
    simp [compileStep,attachTemplate,Nat.add_assoc]

end PlanarHom.FixedGadgetNetwork
