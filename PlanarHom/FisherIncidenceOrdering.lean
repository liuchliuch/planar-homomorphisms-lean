import PlanarHom.FisherCubicWeighted

/-! Actual endpoint occurrences and incidence orderings for arbitrary multigraphs.
An ordering is combinatorial data; no embedding compatibility is inferred. -/
noncomputable section
open Classical
open scoped BigOperators

namespace PlanarHom.MultiGraph
variable {V E : Type*}

/-- One Boolean tag for each of the two endpoint occurrences of an edge. -/
def dartVertex (G : MultiGraph V E) (d : E × Bool) : V :=
  if d.2 then G.dst d.1 else G.src d.1

abbrev VertexDarts (G : MultiGraph V E) (v : V) := {d : E × Bool // G.dartVertex d = v}

theorem selectedDegree_eq_dartCount [Fintype E] (G : MultiGraph V E)
    (A : Finset E) (v : V) :
    G.selectedDegree A v =
      Fintype.card {d : E × Bool // d.1 ∈ A ∧ G.dartVertex d = v} := by
  rw [Fintype.card_subtype, Finset.card_filter]
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_bool, dartVertex, Bool.false_eq_true, ↓reduceIte]
  have hi (e : E) :
      ((if e ∈ A ∧ G.dst e = v then 1 else 0 : ℕ) +
        (if e ∈ A ∧ G.src e = v then 1 else 0)) =
      if e ∈ A then
        ((if G.src e = v then 1 else 0 : ℕ) + (if G.dst e = v then 1 else 0)) else 0 := by
    by_cases he : e ∈ A <;> simp [he, Nat.add_comm]
  simp_rw [hi]
  rw [← Finset.sum_filter]
  simp [selectedDegree]

theorem degree_eq_dartCard [Fintype E] (G : MultiGraph V E) (v : V) :
    G.selectedDegree Finset.univ v = Fintype.card (G.VertexDarts v) := by
  rw [G.selectedDegree_eq_dartCount]
  apply Fintype.card_congr
  exact Equiv.subtypeEquivRight (by simp)

/-- A complete local enumeration of endpoint occurrences. Any geometric theorem
using it must additionally establish compatibility with its plane drawing. -/
structure IncidenceOrdering (G : MultiGraph V E) where
  degree : V → ℕ
  atVertex : ∀ v, Fin (degree v) ≃ G.VertexDarts v

namespace IncidenceOrdering
variable {G : MultiGraph V E}

/-- Global port-to-dart equivalence, retaining both ends of every loop. -/
def darts (o : IncidenceOrdering G) : (Σ v, Fin (o.degree v)) ≃ (E × Bool) :=
  (Equiv.sigmaCongrRight o.atVertex).trans (Equiv.sigmaFiberEquiv G.dartVertex)

@[simp] theorem darts_vertex (o : IncidenceOrdering G) (q : Σ v, Fin (o.degree v)) :
    G.dartVertex (o.darts q) = q.1 := (o.atVertex q.1 q.2).2

@[simp] theorem darts_symm_vertex (o : IncidenceOrdering G) (d : E × Bool) :
    (o.darts.symm d).1 = G.dartVertex d := by
  have h := o.darts_vertex (o.darts.symm d)
  simpa only [Equiv.apply_symm_apply] using h.symm

theorem degree_eq [Fintype E] (o : IncidenceOrdering G) (v : V) :
    o.degree v = G.selectedDegree Finset.univ v := by
  rw [G.degree_eq_dartCard]
  simpa using Fintype.card_congr (o.atVertex v)

def portBits (o : IncidenceOrdering G) (A : Finset E) (v : V) : Fin (o.degree v) → Bool :=
  fun i => decide ((o.darts ⟨v, i⟩).1 ∈ A)

theorem selectedDegree_eq_portBits [Fintype E] (o : IncidenceOrdering G)
    (A : Finset E) (v : V) :
    G.selectedDegree A v = ∑ i, (if o.portBits A v i then 1 else 0 : ℕ) := by
  rw [G.selectedDegree_eq_dartCount]
  let e : {d : E × Bool // d.1 ∈ A ∧ G.dartVertex d = v} ≃
      {d : G.VertexDarts v // d.1.1 ∈ A} :=
    { toFun := fun d => ⟨⟨d.1, d.2.2⟩, d.2.1⟩
      invFun := fun d => ⟨d.1.1, d.2, d.1.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Fintype.card_congr e, Fintype.card_subtype, Finset.card_filter]
  symm
  apply Fintype.sum_equiv (o.atVertex v)
  intro i
  simp [portBits, darts]

end IncidenceOrdering

/-- Every finite input has an incidence ordering. This choice alone supplies
no information about planar cyclic order. -/
def someIncidenceOrdering [Fintype E] (G : MultiGraph V E) : IncidenceOrdering G where
  degree v := Fintype.card (G.VertexDarts v)
  atVertex v := (Fintype.equivFin (G.VertexDarts v)).symm

/-- A cubic multigraph admits the port presentation required by the explicit
Fisher correspondence, proved from its actual occurrence degrees. -/
def cubicPorts [Fintype E] (G : MultiGraph V E)
    (h : ∀ v, G.selectedDegree Finset.univ v = 3) : (V × Fin 3) ≃ (E × Bool) :=
  (Equiv.sigmaEquivProd V (Fin 3)).symm |>.trans
    ((Equiv.sigmaCongrRight (fun v =>
      (Fintype.equivFinOfCardEq ((G.degree_eq_dartCard v).symm.trans (h v))).symm)).trans
      (Equiv.sigmaFiberEquiv G.dartVertex))

theorem cubicPorts_vertex [Fintype E] (G : MultiGraph V E)
    (h : ∀ v, G.selectedDegree Finset.univ v = 3) (d : E × Bool) :
    ((G.cubicPorts h).symm d).1 = G.dartVertex d := rfl

theorem cubicOriginal_cubicPorts [Fintype E] (G : MultiGraph V E)
    (h : ∀ v, G.selectedDegree Finset.univ v = 3) :
    Fisher.cubicOriginal (G.cubicPorts h) = G := by
  cases G
  rfl

end PlanarHom.MultiGraph
