import PlanarHom.FisherPathCorePlanarity
import PlanarHom.FisherLeafAttachments
import PlanarHom.FisherExpansionCorrespondence

/-! Reconstructing the cubic expansion by proved planar leaf and loop attachments. -/
noncomputable section
open Classical

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

def LeafPresent (o : G.IncidenceOrdering) (p : V × Bool) : Prop :=
  o.degree p.1 ≠ 0 ∨ p.2 = true

abbrev ExpansionLeaf (o : G.IncidenceOrdering) := {p : V × Bool // LeafPresent o p}

def expansionLeafRoot (o : G.IncidenceOrdering) (p : ExpansionLeaf o) : PathCoreVertex o :=
  if h : o.degree p.1.1 = 0 then Sum.inr ⟨p.1.1,h⟩ else
    Sum.inl ⟨p.1.1, if p.1.2 then ⟨o.degree p.1.1 - 1, by omega⟩ else ⟨0, by omega⟩⟩

def expansionLoopRoot (o : G.IncidenceOrdering) (p : V × Bool) :
    PathCoreVertex o ⊕ ExpansionLeaf o :=
  if h : LeafPresent o p then Sum.inr ⟨p,h⟩ else
    Sum.inl (Sum.inr ⟨p.1, by simpa [LeafPresent] using (not_or.mp h).1⟩)

def attachedExpansion (o : G.IncidenceOrdering) :=
  ((pathCoreGraph o).addLeaves (expansionLeafRoot o) (fun p => p.1.2)).addIndexedLoops
    (expansionLoopRoot o)

theorem attachedExpansion_planar [Fintype V] [Fintype E] (o : G.IncidenceOrdering)
    (h : (pathCoreGraph o).Planar) : (attachedExpansion o).Planar :=
  (h.addLeaves (expansionLeafRoot o) (fun p => p.1.2)).addIndexedLoops (expansionLoopRoot o)

def expansionVertexMap (o : G.IncidenceOrdering) :
    PathCoreVertex o ⊕ ExpansionLeaf o → ExpansionVertex o :=
  Sum.elim (Sum.elim (portVertex o) (fun v => ⟨v.1,0⟩))
    (fun p => ⟨p.1.1, pathLoopVertex (o.degree p.1.1) p.1.2⟩)

def expansionVertexInverse (o : G.IncidenceOrdering) (q : ExpansionVertex o) :
    PathCoreVertex o ⊕ ExpansionLeaf o :=
  if h0 : q.2 = 0 then
    if hd : o.degree q.1 = 0 then Sum.inl (Sum.inr ⟨q.1,hd⟩)
    else Sum.inr ⟨(q.1,false), Or.inl hd⟩
  else if hl : q.2 = Fin.last (o.degree q.1 + 1) then
    Sum.inr ⟨(q.1,true), Or.inr rfl⟩
  else Sum.inl (Sum.inl ⟨q.1, ⟨q.2.val - 1, by
    have hj := q.2.isLt
    have h0' : q.2.val ≠ 0 := fun h => h0 (Fin.ext h)
    have hl' : q.2.val ≠ o.degree q.1 + 1 := fun h => hl (Fin.ext h)
    omega⟩⟩)

theorem expansionVertexInverse_map (o : G.IncidenceOrdering)
    (q : PathCoreVertex o ⊕ ExpansionLeaf o) :
    expansionVertexInverse o (expansionVertexMap o q) = q := by
  rcases q with ((⟨v,i⟩ | v) | ⟨⟨v,b⟩,hb⟩)
  · have h0 : i.succ.castSucc ≠ (0 : Fin (o.degree v + 2)) := by
      intro h
      have hh := congrArg Fin.val h
      change i.val + 1 = 0 at hh
      omega
    have hl : i.succ.castSucc ≠ Fin.last (o.degree v + 1) := by
      intro h
      have hh := congrArg Fin.val h
      change i.val + 1 = o.degree v + 1 at hh
      omega
    simp only [expansionVertexMap, Sum.elim_inl, portVertex, expansionVertexInverse,
      h0, hl, ↓reduceDIte]
    congr 3
  · simp [expansionVertexMap, expansionVertexInverse, v.2]
  · cases b
    · have hd : o.degree v ≠ 0 := by simpa [LeafPresent] using hb
      simp [expansionVertexMap, expansionVertexInverse, pathLoopVertex, hd]
    · have hl : (Fin.last (o.degree v + 1) : Fin (o.degree v + 2)) ≠ 0 := by
        intro h
        have hh := congrArg Fin.val h
        change o.degree v + 1 = 0 at hh
        omega
      simp [expansionVertexMap, expansionVertexInverse, pathLoopVertex, hl]

theorem expansionVertexMap_inverse (o : G.IncidenceOrdering) (q : ExpansionVertex o) :
    expansionVertexMap o (expansionVertexInverse o q) = q := by
  rcases q with ⟨v,j⟩
  by_cases h0 : j = 0
  · subst j
    by_cases hd : o.degree v = 0 <;>
      simp [expansionVertexInverse, expansionVertexMap, hd, pathLoopVertex]
  · by_cases hl : j = Fin.last (o.degree v + 1)
    · subst j
      simp [expansionVertexInverse, expansionVertexMap, h0, pathLoopVertex]
    · simp only [expansionVertexInverse, h0, hl, ↓reduceDIte, expansionVertexMap,
        Sum.elim_inl, portVertex]
      congr 1
      apply Fin.ext
      have hj : j.val ≠ 0 := fun h => h0 (Fin.ext h)
      change j.val - 1 + 1 = j.val
      omega

def expansionVertexEquiv (o : G.IncidenceOrdering) :
    PathCoreVertex o ⊕ ExpansionLeaf o ≃ ExpansionVertex o where
  toFun := expansionVertexMap o
  invFun := expansionVertexInverse o
  left_inv := expansionVertexInverse_map o
  right_inv := expansionVertexMap_inverse o

abbrev AttachedExpansionEdge (o : G.IncidenceOrdering) :=
  (PathCoreEdge o ⊕ ExpansionLeaf o) ⊕ (V × Bool)

def expansionEdgeMap (o : G.IncidenceOrdering) : AttachedExpansionEdge o → ExpansionEdge o :=
  Sum.elim (Sum.elim (Sum.elim Sum.inl
    (fun q => Sum.inr ⟨q.1, Sum.inl ⟨q.2.val + 1, by have := q.2.isLt; omega⟩⟩))
    (fun p => Sum.inr ⟨p.1.1, Sum.inl (if p.1.2 then Fin.last (o.degree p.1.1) else 0)⟩))
    (fun p => Sum.inr ⟨p.1, Sum.inr p.2⟩)

def expansionEdgeInverse (o : G.IncidenceOrdering) : ExpansionEdge o → AttachedExpansionEdge o :=
  Sum.elim (fun e => Sum.inl (Sum.inl (Sum.inl e)))
    (fun q => match q with
      | ⟨v,Sum.inr b⟩ => Sum.inr (v,b)
      | ⟨v,Sum.inl k⟩ =>
        if hl : k = Fin.last (o.degree v) then Sum.inl (Sum.inr ⟨(v,true),Or.inr rfl⟩)
        else if h0 : k = 0 then Sum.inl (Sum.inr ⟨(v,false),Or.inl (by
          intro hd
          apply hl
          apply Fin.ext
          simpa [hd] using congrArg Fin.val h0)⟩)
        else Sum.inl (Sum.inl (Sum.inr ⟨v,⟨k.val - 1, by
          have hk := k.isLt
          have h0' : k.val ≠ 0 := fun h => h0 (Fin.ext h)
          have hl' : k.val ≠ o.degree v := fun h => hl (Fin.ext h)
          omega⟩⟩)))

theorem expansionEdgeInverse_map (o : G.IncidenceOrdering) (e : AttachedExpansionEdge o) :
    expansionEdgeInverse o (expansionEdgeMap o e) = e := by
  rcases e with (((e | ⟨v,k⟩) | ⟨⟨v,b⟩,hb⟩) | ⟨v,b⟩)
  · rfl
  · have hl : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (o.degree v + 1)) ≠
        Fin.last (o.degree v) := by
      intro h
      have hh := congrArg Fin.val h
      change k.val + 1 = o.degree v at hh
      omega
    have h0 : (⟨k.val + 1, by have := k.isLt; omega⟩ : Fin (o.degree v + 1)) ≠ 0 := by
      intro h
      have hh := congrArg Fin.val h
      change k.val + 1 = 0 at hh
      omega
    simp only [expansionEdgeMap, Sum.elim_inl, Sum.elim_inr, expansionEdgeInverse,
      hl, h0, ↓reduceDIte]
    congr 4
  · cases b
    · have hd : o.degree v ≠ 0 := by simpa [LeafPresent] using hb
      have hl : (0 : Fin (o.degree v + 1)) ≠ Fin.last (o.degree v) := by
        intro h
        have hh := congrArg Fin.val h
        change 0 = o.degree v at hh
        exact hd hh.symm
      simp [expansionEdgeMap, expansionEdgeInverse, hl]
    · simp [expansionEdgeMap, expansionEdgeInverse]
  · rfl

theorem expansionEdgeMap_inverse (o : G.IncidenceOrdering) (e : ExpansionEdge o) :
    expansionEdgeMap o (expansionEdgeInverse o e) = e := by
  rcases e with (e | ⟨v,k | b⟩)
  · rfl
  · by_cases hl : k = Fin.last (o.degree v)
    · subst k
      simp [expansionEdgeInverse, expansionEdgeMap]
    · by_cases h0 : k = 0
      · subst k
        simp [expansionEdgeInverse, expansionEdgeMap, hl]
      · simp only [expansionEdgeInverse, hl, h0, ↓reduceDIte, expansionEdgeMap,
          Sum.elim_inl, Sum.elim_inr]
        congr 3
        apply Fin.ext
        change k.val - 1 + 1 = k.val
        have hk : k.val ≠ 0 := fun h => h0 (Fin.ext h)
        omega
  · rfl

def expansionEdgeEquiv (o : G.IncidenceOrdering) : AttachedExpansionEdge o ≃ ExpansionEdge o where
  toFun := expansionEdgeMap o
  invFun := expansionEdgeInverse o
  left_inv := expansionEdgeInverse_map o
  right_inv := expansionEdgeMap_inverse o

theorem expansionVertexMap_leafRoot (o : G.IncidenceOrdering) (p : ExpansionLeaf o) :
    expansionVertexMap o (Sum.inl (expansionLeafRoot o p)) =
      ⟨p.1.1, ⟨if p.1.2 then o.degree p.1.1 else 1, by split <;> omega⟩⟩ := by
  rcases p with ⟨⟨v,b⟩,hp⟩
  by_cases hd : o.degree v = 0
  · have hb : b = true := by simpa [LeafPresent, hd] using hp
    subst b
    simp [expansionLeafRoot, expansionVertexMap, hd]
  · cases b <;> simp [expansionLeafRoot, expansionVertexMap, hd, portVertex]
    omega

theorem expansionVertexMap_loopRoot (o : G.IncidenceOrdering) (p : V × Bool) :
    expansionVertexMap o (expansionLoopRoot o p) =
      ⟨p.1, pathLoopVertex (o.degree p.1) p.2⟩ := by
  by_cases hp : LeafPresent o p
  · simp [expansionLoopRoot, expansionVertexMap, hp]
  · have hb : p.2 = false := by
      have h := (not_or.mp hp).2
      cases hpb : p.2 <;> simp_all
    simp [expansionLoopRoot, expansionVertexMap, hp, hb, pathLoopVertex]

/-- Exact endpoint-preserving identification of the attached graph with the
previously audited cubic expansion, including the isolate endpoint convention. -/
def attachedExpansionEquiv (o : G.IncidenceOrdering) :
    IncidenceEquiv (attachedExpansion o) (expansionGraph o) where
  vertex := expansionVertexEquiv o
  edge := expansionEdgeEquiv o
  src_eq := by
    rintro (((e | ⟨v,k⟩) | p) | ⟨v,b⟩)
    · rfl
    · rfl
    · cases hb : p.1.2
      · simp [expansionEdgeEquiv, expansionEdgeMap, expansionVertexEquiv, expansionVertexMap,
          attachedExpansion, addLeaves, addIndexedLoops, expansionGraph, localExpansion,
          pathLoopVertex, hb]
      · simp only [expansionEdgeEquiv, Equiv.coe_fn_mk, expansionEdgeMap, Sum.elim_inl,
          Sum.elim_inr, hb, ↓reduceIte, expansionGraph, localExpansion,
          attachedExpansion, addLeaves, addIndexedLoops, expansionVertexEquiv]
        simpa [hb] using (expansionVertexMap_leafRoot o p).symm
    · exact (expansionVertexMap_loopRoot o (v,b)).symm
  dst_eq := by
    rintro (((e | ⟨v,k⟩) | p) | ⟨v,b⟩)
    · rfl
    · rfl
    · cases hb : p.1.2
      · simp only [expansionEdgeEquiv, Equiv.coe_fn_mk, expansionEdgeMap, Sum.elim_inl,
          Sum.elim_inr, hb, ↓reduceIte, expansionGraph, localExpansion,
          attachedExpansion, addLeaves, addIndexedLoops, expansionVertexEquiv]
        simpa [hb] using (expansionVertexMap_leafRoot o p).symm
      · simp [expansionEdgeEquiv, expansionEdgeMap, expansionVertexEquiv, expansionVertexMap,
          attachedExpansion, addLeaves, addIndexedLoops, expansionGraph, localExpansion,
          pathLoopVertex, hb]
    · exact (expansionVertexMap_loopRoot o (v,b)).symm

theorem expansion_planar_of_pathCore [Fintype V] [Fintype E] (o : G.IncidenceOrdering)
    (h : (pathCoreGraph o).Planar) : (expansionGraph o).Planar :=
  (attachedExpansionEquiv o).planar_iff.mp (attachedExpansion_planar o h)

/-- Actual ordinary planar inputs admit a cubic expansion with the exact
previously proved even-subgraph correspondence. No ordering is input data. -/
theorem exists_planar_expansion [Fintype V] [Fintype E] (hG : G.Planar) :
    ∃ o : G.IncidenceOrdering, (expansionGraph o).Planar := by
  obtain ⟨o, ho⟩ := exists_planar_pathCore hG
  exact ⟨o, expansion_planar_of_pathCore o ho⟩

end PlanarHom.Fisher
