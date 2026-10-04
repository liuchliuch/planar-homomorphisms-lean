import PlanarHom.FisherTriangle
import PlanarHom.OccurrenceMatchings

/-!
# An occurrence-labelled Fisher graph for a cubic incidence presentation

A port equivalence identifies every original endpoint occurrence with exactly
one of three ports at a vertex. The decoration uses an actual triangle at every
original vertex and retains every original edge occurrence as an external edge.
-/

noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.Fisher
variable {V E : Type*}

/-- The original multigraph encoded by its three ports per vertex. -/
def cubicOriginal (p : (V × Fin 3) ≃ (E × Bool)) : MultiGraph V E where
  src e := (p.symm (e, false)).1
  dst e := (p.symm (e, true)).1

/-- The literal decorated graph. External edge occurrences retain their labels;
the other occurrences are the three triangle edges at each original vertex. -/
def cubicDecoration (p : (V × Fin 3) ≃ (E × Bool)) :
    MultiGraph (V × Fin 3) (E ⊕ (V × Fin 3)) where
  src := Sum.elim (fun e => p.symm (e, false)) (fun q => (q.1, triangle.src q.2))
  dst := Sum.elim (fun e => p.symm (e, true)) (fun q => (q.1, triangle.dst q.2))

/-- The terminals covered by selected external edge occurrences. -/
def selectedPorts (p : (V × Fin 3) ≃ (E × Bool)) (B : Finset E) (v : V) :
    Finset (Fin 3) := Finset.univ.filter (fun i => (p (v, i)).1 ∈ B)

/-- All chosen internal triangle edges, with the original vertex retained. -/
def internalEdges [Fintype V] (m : V → Finset (Fin 3)) : Finset (V × Fin 3) :=
  Finset.univ.filter (fun q => q.2 ∈ m q.1)

/-- The actual subset of decorated edge occurrences determined by external
and local internal choices. -/
def decoratedEdges [Fintype V] (B : Finset E) (m : V → Finset (Fin 3)) :
    Finset (E ⊕ (V × Fin 3)) := B.disjSum (internalEdges m)

theorem external_incidence (p : (V × Fin 3) ≃ (E × Bool))
    (e : E) (q : V × Fin 3) :
    ((if p.symm (e, false) = q then 1 else 0 : ℕ) +
      (if p.symm (e, true) = q then 1 else 0)) =
        if e = (p q).1 then 1 else 0 := by
  simp only [Equiv.symm_apply_eq]
  rcases h : p q with ⟨e', b⟩
  cases b <;> simp [Prod.mk.injEq, eq_comm]

theorem external_degree (p : (V × Fin 3) ≃ (E × Bool))
    (B : Finset E) (q : V × Fin 3) :
    (∑ e ∈ B, ((if p.symm (e, false) = q then 1 else 0 : ℕ) +
      (if p.symm (e, true) = q then 1 else 0))) =
        if (p q).1 ∈ B then 1 else 0 := by
  simp_rw [external_incidence]
  simp

theorem internal_degree [Fintype V] (m : V → Finset (Fin 3)) (v : V) (i : Fin 3) :
    (∑ q ∈ internalEdges m,
      ((if (q.1, triangle.src q.2) = (v, i) then 1 else 0 : ℕ) +
        (if (q.1, triangle.dst q.2) = (v, i) then 1 else 0))) =
      triangle.selectedDegree (m v) i := by
  simp only [internalEdges, Finset.sum_filter, Fintype.sum_prod_type, Prod.mk.injEq]
  have h (u : V) (j : Fin 3) :
      (if j ∈ m u then
        ((if u = v ∧ triangle.src j = i then 1 else 0 : ℕ) +
          (if u = v ∧ triangle.dst j = i then 1 else 0)) else 0) =
      if u = v then (if j ∈ m v then
        ((if triangle.src j = i then 1 else 0 : ℕ) +
          (if triangle.dst j = i then 1 else 0)) else 0) else 0 := by
    by_cases hu : u = v
    · subst u
      simp
    · simp [hu]
  simp_rw [h, Finset.sum_ite_irrel]
  simp only [Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  rw [← Finset.sum_filter]
  simp [MultiGraph.selectedDegree]
  apply Finset.sum_congr rfl
  intro e _
  apply congrArg₂ Nat.add <;> split_ifs <;> rfl

/-- Local incidence constraints are exactly the perfect-matching constraints
of the constructed graph. -/
theorem decorated_degree [Fintype V] (p : (V × Fin 3) ≃ (E × Bool))
    (B : Finset E) (m : V → Finset (Fin 3)) (v : V) (i : Fin 3) :
    (cubicDecoration p).selectedDegree (decoratedEdges B m) (v, i) =
      (if i ∈ selectedPorts p B v then 1 else 0) + triangle.selectedDegree (m v) i := by
  conv_lhs => unfold MultiGraph.selectedDegree
  simp only [decoratedEdges, Finset.sum_disjSum,
    cubicDecoration, Sum.elim_inl, Sum.elim_inr]
  calc
    _ = (if (p (v, i)).1 ∈ B then 1 else 0) + triangle.selectedDegree (m v) i := by
      apply congrArg₂ Nat.add
      · convert external_degree p B (v, i) using 1
        apply Finset.sum_congr rfl
        intro e _
        apply congrArg₂ Nat.add <;> split_ifs <;> rfl
      · convert internal_degree m v i using 1
        apply Finset.sum_congr rfl
        intro e _
        apply congrArg₂ Nat.add <;> split_ifs <;> rfl
    _ = _ := by simp [selectedPorts]

theorem decorated_perfectMatching_iff [Fintype V]
    (p : (V × Fin 3) ≃ (E × Bool)) (B : Finset E) (m : V → Finset (Fin 3)) :
    (cubicDecoration p).PerfectMatching (decoratedEdges B m) ↔
      ∀ v, TriangleCompatible (selectedPorts p B v) (m v) := by
  simp only [MultiGraph.PerfectMatching, Prod.forall, decorated_degree,
    triangleCompatible_iff_degree, Nat.add_comm]

theorem sum_port_incidence (q : V × Fin 3) (v : V) :
    (∑ i : Fin 3, (if q = (v, i) then 1 else 0 : ℕ)) =
      if q.1 = v then 1 else 0 := by
  rcases q with ⟨u, j⟩
  by_cases h : u = v
  · subst u
    simp [Prod.mk.injEq]
  · simp [Prod.mk.injEq, h]

/-- The original degree is the number of its selected endpoint ports. In
particular a loop contributes both of its different ports at the vertex. -/
theorem original_degree_eq_ports (p : (V × Fin 3) ≃ (E × Bool))
    (A : Finset E) (v : V) :
    (cubicOriginal p).selectedDegree A v = (selectedPorts p A v).card := by
  calc
    _ = ∑ e ∈ A, ∑ i : Fin 3,
        ((if p.symm (e, false) = (v, i) then 1 else 0 : ℕ) +
          (if p.symm (e, true) = (v, i) then 1 else 0)) := by
      unfold MultiGraph.selectedDegree
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_add_distrib, sum_port_incidence, sum_port_incidence]
      rfl
    _ = ∑ i : Fin 3, ∑ e ∈ A,
        ((if p.symm (e, false) = (v, i) then 1 else 0 : ℕ) +
          (if p.symm (e, true) = (v, i) then 1 else 0)) := Finset.sum_comm
    _ = ∑ i : Fin 3, if (p (v, i)).1 ∈ A then 1 else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      exact external_degree p A (v, i)
    _ = _ := by exact Finset.sum_boole _ _

theorem selectedPorts_compl [Fintype E] (p : (V × Fin 3) ≃ (E × Bool))
    (A : Finset E) (v : V) :
    selectedPorts p Aᶜ v = (selectedPorts p A v)ᶜ := by
  ext i
  simp [selectedPorts]

/-- Each original even subgraph determines precisely one tuple of internal
triangle completions, giving an actual perfect matching of the decorated graph. -/
theorem cubic_matching_completion_iff [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (A : Finset E) (m : V → Finset (Fin 3)) :
    (cubicDecoration p).PerfectMatching (decoratedEdges Aᶜ m) ↔
      (cubicOriginal p).EvenSubgraph A ∧
        m = fun v => triangleCompletion (selectedPorts p Aᶜ v) := by
  rw [decorated_perfectMatching_iff]
  simp_rw [selectedPorts_compl, triangle_even_completion_iff]
  simp only [MultiGraph.EvenSubgraph, original_degree_eq_ports]
  constructor
  · intro h
    exact ⟨fun v => (h v).1, funext fun v => (h v).2⟩
  · rintro ⟨h, rfl⟩ v
    exact ⟨h v, rfl⟩

theorem existsUnique_cubic_matching_completion [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (A : Finset E) :
    (∃! m, (cubicDecoration p).PerfectMatching (decoratedEdges Aᶜ m)) ↔
      (cubicOriginal p).EvenSubgraph A := by
  simp_rw [cubic_matching_completion_iff]
  constructor
  · rintro ⟨m, ⟨h, _⟩, _⟩
    exact h
  · intro h
    exact ⟨_, ⟨h, rfl⟩, fun _ hm => hm.2⟩

/-- Read the internal occurrences at one original vertex from any decorated set. -/
def readInternal (M : Finset (E ⊕ (V × Fin 3))) (v : V) : Finset (Fin 3) :=
  Finset.univ.filter (fun i => Sum.inr (v, i) ∈ M)

@[simp] theorem toLeft_decoratedEdges [Fintype V]
    (B : Finset E) (m : V → Finset (Fin 3)) :
    (decoratedEdges B m).toLeft = B := by simp [decoratedEdges]

@[simp] theorem readInternal_decoratedEdges [Fintype V]
    (B : Finset E) (m : V → Finset (Fin 3)) :
    readInternal (decoratedEdges B m) = m := by
  funext v
  ext i
  simp [readInternal, decoratedEdges, internalEdges]

theorem decoratedEdges_read [Fintype V] (M : Finset (E ⊕ (V × Fin 3))) :
    decoratedEdges M.toLeft (readInternal M) = M := by
  ext q
  cases q <;> simp [decoratedEdges, internalEdges, readInternal]

/-- Every edge occurrence set has an exact external/local decomposition. -/
def decorationEdgeSetEquiv [Fintype V] :
    (Finset E × (V → Finset (Fin 3))) ≃ Finset (E ⊕ (V × Fin 3)) where
  toFun s := decoratedEdges s.1 s.2
  invFun M := (M.toLeft, readInternal M)
  left_inv s := by simp
  right_inv M := decoratedEdges_read M

theorem perfectMatching_read_even [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) (M : Finset (E ⊕ (V × Fin 3)))
    (hM : (cubicDecoration p).PerfectMatching M) :
    (cubicOriginal p).EvenSubgraph M.toLeftᶜ ∧
      readInternal M = fun v => triangleCompletion (selectedPorts p M.toLeft v) := by
  have h := (cubic_matching_completion_iff p M.toLeftᶜ (readInternal M)).mp
    (by simpa only [compl_compl, decoratedEdges_read] using hM)
  simpa only [compl_compl] using h

/-- Fisher's actual finite bijection for a cubic incidence presentation.
It relates all even occurrence subsets to all perfect matching occurrence sets. -/
def cubicFisherEquiv [Fintype V] [Fintype E]
    (p : (V × Fin 3) ≃ (E × Bool)) :
    {A : Finset E // (cubicOriginal p).EvenSubgraph A} ≃
      {M : Finset (E ⊕ (V × Fin 3)) // (cubicDecoration p).PerfectMatching M} where
  toFun A := ⟨decoratedEdges A.1ᶜ (fun v => triangleCompletion (selectedPorts p A.1ᶜ v)),
    (cubic_matching_completion_iff p A.1 _).mpr ⟨A.2, rfl⟩⟩
  invFun M := ⟨M.1.toLeftᶜ, (perfectMatching_read_even p M.1 M.2).1⟩
  left_inv A := by
    apply Subtype.ext
    simp
  right_inv M := by
    apply Subtype.ext
    change decoratedEdges M.1.toLeftᶜᶜ
      (fun v => triangleCompletion (selectedPorts p M.1.toLeftᶜᶜ v)) = M.1
    rw [compl_compl, ← (perfectMatching_read_even p M.1 M.2).2, decoratedEdges_read]

end PlanarHom.Fisher
