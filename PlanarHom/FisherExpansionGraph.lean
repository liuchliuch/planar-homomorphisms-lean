import PlanarHom.FisherLocalExpansion

/-! An actual cubic expansion for an explicitly ordered finite multigraph. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
open MultiGraph
variable {V E : Type*} {G : MultiGraph V E}

abbrev ExpansionVertex (o : IncidenceOrdering G) := Σ v, Fin (o.degree v + 2)
abbrev ExpansionInternalEdge (o : IncidenceOrdering G) := Σ v, Fin (o.degree v + 1) ⊕ Bool
abbrev ExpansionEdge (o : IncidenceOrdering G) := E ⊕ ExpansionInternalEdge o

/-- The vertex carrying one original endpoint occurrence. -/
def portVertex (o : IncidenceOrdering G) (q : Σ v, Fin (o.degree v)) : ExpansionVertex o :=
  ⟨q.1, q.2.succ.castSucc⟩

theorem portVertex_injective (o : IncidenceOrdering G) : Function.Injective (portVertex o) := by
  rintro ⟨v, i⟩ ⟨w, j⟩ h
  obtain ⟨rfl, hij⟩ := Sigma.mk.inj_iff.mp h
  apply congrArg (Sigma.mk v)
  exact (Fin.succ_injective _) ((Fin.castSucc_injective _) (eq_of_heq hij))

theorem portVertex_ne_zero (o : IncidenceOrdering G) (q : Σ v, Fin (o.degree v)) (v : V) :
    portVertex o q ≠ ⟨v, 0⟩ := by
  rcases q with ⟨u, i⟩
  intro h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp h
  have hv := congrArg Fin.val (eq_of_heq hi)
  change i.val + 1 = 0 at hv
  omega

theorem portVertex_ne_last (o : IncidenceOrdering G) (q : Σ v, Fin (o.degree v)) (v : V) :
    portVertex o q ≠ ⟨v, Fin.last (o.degree v + 1)⟩ := by
  rcases q with ⟨u, i⟩
  intro h
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj_iff.mp h
  have hv := congrArg Fin.val (eq_of_heq hi)
  change i.val + 1 = o.degree u + 1 at hv
  omega

/-- Original edges join their own endpoint ports. Each vertex is replaced by
the local path and two loops, including a degree-zero vertex. -/
def expansionGraph (o : IncidenceOrdering G) : MultiGraph (ExpansionVertex o) (ExpansionEdge o) where
  src := Sum.elim (fun e => portVertex o (o.darts.symm (e, false)))
    (fun e => ⟨e.1, (localExpansion (o.degree e.1)).src e.2⟩)
  dst := Sum.elim (fun e => portVertex o (o.darts.symm (e, true)))
    (fun e => ⟨e.1, (localExpansion (o.degree e.1)).dst e.2⟩)

def expansionInternalSet [Fintype V] (o : IncidenceOrdering G)
    (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) : Finset (ExpansionInternalEdge o) :=
  Finset.univ.filter (fun e => e.2 ∈ m e.1)

def expansionSet [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) : Finset (ExpansionEdge o) :=
  A.disjSum (expansionInternalSet o m)

def originalContribution (o : IncidenceOrdering G) (A : Finset E) (q : ExpansionVertex o) : ℕ :=
  ∑ e ∈ A, ((if portVertex o (o.darts.symm (e, false)) = q then 1 else 0) +
    (if portVertex o (o.darts.symm (e, true)) = q then 1 else 0))

@[simp] theorem originalContribution_zero (o : IncidenceOrdering G) (A : Finset E) (v : V) :
    originalContribution o A ⟨v, 0⟩ = 0 := by
  simp [originalContribution, portVertex_ne_zero]

@[simp] theorem originalContribution_last (o : IncidenceOrdering G) (A : Finset E) (v : V) :
    originalContribution o A ⟨v, Fin.last (o.degree v + 1)⟩ = 0 := by
  simp [originalContribution, portVertex_ne_last]

theorem originalContribution_port (o : IncidenceOrdering G) (A : Finset E)
    (q : Σ v, Fin (o.degree v)) :
    originalContribution o A (portVertex o q) = if (o.darts q).1 ∈ A then 1 else 0 := by
  unfold originalContribution
  simp only [(portVertex_injective o).eq_iff, Equiv.symm_apply_eq]
  rcases h : o.darts q with ⟨e, b⟩
  cases b <;> simp [Prod.mk.injEq]

theorem expansion_degree [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (m : ∀ v, Finset (Fin (o.degree v + 1) ⊕ Bool)) (v : V) (j : Fin (o.degree v + 2)) :
    (expansionGraph o).selectedDegree (expansionSet o A m) ⟨v, j⟩ =
      originalContribution o A ⟨v, j⟩ + (localExpansion (o.degree v)).selectedDegree (m v) j := by
  unfold MultiGraph.selectedDegree
  simp only [expansionSet, Finset.sum_disjSum, expansionGraph, Sum.elim_inl, Sum.elim_inr]
  apply congrArg₂ Nat.add
  · unfold originalContribution
    apply Finset.sum_congr rfl
    intro e _
    apply congrArg₂ Nat.add <;> split_ifs <;> rfl
  · simp only [expansionInternalSet, Finset.sum_filter, Fintype.sum_sigma]
    rw [Finset.sum_eq_single v]
    · simp only [Sigma.mk.inj_iff, true_and, heq_eq_eq]
      rw [← Finset.sum_filter]
      simp
      apply Finset.sum_congr rfl
      intro e _
      apply congrArg₂ Nat.add <;> split_ifs <;> rfl
    · intro u _ huv
      apply Finset.sum_eq_zero
      intro e _
      have hs : (⟨u, (localExpansion (o.degree u)).src e⟩ : ExpansionVertex o) ≠ ⟨v, j⟩ := by
        intro h
        exact huv (congrArg Sigma.fst h)
      have hd : (⟨u, (localExpansion (o.degree u)).dst e⟩ : ExpansionVertex o) ≠ ⟨v, j⟩ := by
        intro h
        exact huv (congrArg Sigma.fst h)
      simp [hs, hd]
    · simp

@[simp] theorem expansionSet_univ [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    expansionSet o Finset.univ (fun _ => Finset.univ) = Finset.univ := by
  ext e
  cases e <;> simp [expansionSet, expansionInternalSet]

/-- Every expanded vertex has exactly three endpoint occurrences, including
the degree-zero, degree-one, and degree-two input cases. -/
theorem expansion_is_cubic [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    ∀ q, (expansionGraph o).selectedDegree Finset.univ q = 3 := by
  rintro ⟨v, j⟩
  rw [← expansionSet_univ o, expansion_degree]
  have hu : (Finset.univ : Finset (Fin (o.degree v + 1) ⊕ Bool)) =
      (Finset.univ : Finset (Fin (o.degree v + 1))).disjSum Finset.univ := by
    ext e
    cases e <;> simp
  have hall : ∀ j : Fin (o.degree v + 2),
      originalContribution o Finset.univ ⟨v, j⟩ +
        (localExpansion (o.degree v)).selectedDegree Finset.univ j = 3 := by
    apply (forall_fin_endpoints (d := o.degree v) (fun j =>
      originalContribution o Finset.univ ⟨v, j⟩ +
        (localExpansion (o.degree v)).selectedDegree Finset.univ j = 3)).mpr
    refine ⟨?_, ?_, ?_⟩
    · rw [originalContribution_zero, hu, local_degree_zero]
      simp
    · rw [originalContribution_last, hu, local_degree_last]
      simp
    · intro i
      have ho := originalContribution_port o Finset.univ ⟨v, i⟩
      change originalContribution o Finset.univ ⟨v, i.succ.castSucc⟩ = _ at ho
      rw [ho, hu, local_degree_interior]
      simp
  exact hall j

/-- The derived cubic port equivalence comes from actual incidence counts. -/
def expansionCubicPorts [Fintype V] [Fintype E] (o : IncidenceOrdering G) :
    (ExpansionVertex o × Fin 3) ≃ (ExpansionEdge o × Bool) :=
  (expansionGraph o).cubicPorts (expansion_is_cubic o)

@[simp] theorem cubicOriginal_expansionCubicPorts [Fintype V] [Fintype E]
    (o : IncidenceOrdering G) : cubicOriginal (expansionCubicPorts o) = expansionGraph o :=
  (expansionGraph o).cubicOriginal_cubicPorts (expansion_is_cubic o)

theorem expansion_even_iff_local [Fintype V] (o : IncidenceOrdering G) (A : Finset E)
    (P : ∀ v, Finset (Fin (o.degree v + 1))) (L : V → Finset Bool) :
    (expansionGraph o).EvenSubgraph (expansionSet o A (fun v => (P v).disjSum (L v))) ↔
      ∀ v, LocalEven (o.portBits A v) (P v) (L v) := by
  simp only [MultiGraph.EvenSubgraph, Sigma.forall, expansion_degree]
  apply forall_congr'
  intro v
  rw [forall_fin_endpoints]
  have ho (i : Fin (o.degree v)) :
      originalContribution o A ⟨v, i.succ.castSucc⟩ =
        (if o.portBits A v i then 1 else 0 : ℕ) := by
    simpa [portVertex, IncidenceOrdering.portBits] using originalContribution_port o A ⟨v, i⟩
  simp only [originalContribution_zero, originalContribution_last, zero_add, LocalEven, ho,
    Nat.add_comm]

/-- The expanded even subsets have exactly one forced path per vertex and
two unconstrained endpoint-loop bits per vertex. -/
theorem expansion_even_iff [Fintype V] [Fintype E] (o : IncidenceOrdering G) (A : Finset E)
    (P : ∀ v, Finset (Fin (o.degree v + 1))) (L : V → Finset Bool) :
    (expansionGraph o).EvenSubgraph (expansionSet o A (fun v => (P v).disjSum (L v))) ↔
      G.EvenSubgraph A ∧ ∀ v, P v = parityEdges (o.portBits A v) := by
  rw [expansion_even_iff_local]
  simp_rw [localEven_iff, ← o.selectedDegree_eq_portBits]
  exact forall_and

end PlanarHom.Fisher
