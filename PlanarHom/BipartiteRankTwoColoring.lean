import PlanarHom.BipartiteRankTwoMatrix
import PlanarHom.PlanarityParityPolynomial
import PlanarHom.HomogeneousSourceOrientationSemantics

/-! NEW actual bipartition computation for arbitrary raw occurrence graphs.
Each occurrence supplies one binary parity equation; a loop is a contradictory
self equation. The solver computes its own assignment and success flag. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.BipartiteRankTwoTractability
open Complexity Complexity.MixedCode PairProjectionMachines PlanarityParitySolver

abbrev Edge := ℕ × (ℕ × ℕ)
abbrev edgeCode := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

def edgeConstraint (e : Edge) : Constraint := (e.1,e.2.1,true)
def constraints (g : MixedCode) : List Constraint := g.edges.map edgeConstraint
def coloring (g : MixedCode) : Bool × Assignment := computed (constraints g)
def Proper (g : MixedCode) (δ : ℕ → Bool) : Prop := ∀e∈g.edges,δ e.1≠δ e.2.1

theorem holds_edge_iff (δ : ℕ → Bool) (e : Edge) : Holds δ (edgeConstraint e) ↔ δ e.1≠δ e.2.1 := by
  cases h1 : δ e.1 <;> cases h2 : δ e.2.1 <;> simp [Holds,edgeConstraint,h1,h2]

theorem satisfies_iff (g : MixedCode) (δ : ℕ → Bool) : Satisfies δ (constraints g) ↔ Proper g δ := by
  constructor
  · intro h e he
    exact (holds_edge_iff δ e).mp (h _ (List.mem_map.mpr ⟨e,he,rfl⟩))
  · intro h e he
    obtain ⟨f,hf,rfl⟩ := List.mem_map.mp he
    exact (holds_edge_iff δ f).mpr (h f hf)

theorem coloring_sound (g : MixedCode) (h : (coloring g).1=true) : Proper g (lookup (coloring g).2) :=
  (satisfies_iff g _).mp (computed_sound (constraints g) h)

theorem coloring_complete (g : MixedCode) : (coloring g).1=true ↔ ∃δ,Proper g δ := by
  rw [coloring,computed_complete]
  exact exists_congr (fun δ=>satisfies_iff g δ)

theorem fp_edgeConstraint : FP edgeCode constraintCode edgeConstraint :=
  (fp_fst _ _).pair (((fp_snd _ _).comp (fp_fst _ _)).pair (fp_const _ BitEncoding.bool true))

theorem fp_coloring : FP encoding (BitEncoding.bool.prod assignmentCode) coloring :=
  (MixedCode.fp_edges.comp (ListMapMachines.fp_map edgeCode constraintCode edgeConstraint fp_edgeConstraint)).comp fp_computed

theorem proper_not (g : MixedCode) {δ : ℕ → Bool} (h : Proper g δ) : Proper g (fun v=>!(δ v)) := by
  intro e he hn
  apply h e he
  have hh := congrArg Bool.not hn
  simpa only [Bool.not_not] using hh

theorem proper_support (g : MixedCode) (hg : g.Valid 1 0) (δ : ℕ → Bool) (h : Proper g δ) :
    ∀u v,(GraphComponentCode.support g).Adj u v → δ u.val≠δ v.val := by
  intro u v huv
  obtain ⟨_,e,he,hends|hends⟩ := huv
  · simpa only [hends.1,hends.2] using h e he
  · simpa only [hends.1,hends.2] using (h e he).symm

variable {k l : ℕ} {K : Type} [Field K]

def side : Fin k ⊕ Fin l → Bool := Sum.elim (fun _=>false) (fun _=>true)

theorem matrix_crosses (a : Fin k → K) (b : Fin l → K) :
    ∀i j,matrix a b i j≠0 → side i≠side j := by
  intro i j h
  cases i <;> cases j <;> simp_all [matrix,side]

def assignmentSide (g : MixedCode) (σ : Fin g.vertices → Fin k ⊕ Fin l) (v : ℕ) : Bool :=
  if h : v<g.vertices then side (σ ⟨v,h⟩) else false

theorem nonzero_assignment_proper (g : MixedCode) (hg : g.Valid 1 0)
    (a : Fin k → K) (b : Fin l → K) (w : Fin k ⊕ Fin l → K)
    (σ : Fin g.vertices → Fin k ⊕ Fin l)
    (h : (g.toMultiGraph hg).assignmentWeight (matrix a b) w σ≠0) :
    Proper g (assignmentSide g σ) := by
  intro e he
  obtain ⟨n,hn⟩ := List.get_of_mem he
  have hv := hg.1 e he
  have hz := RootedRestriction.assignment_edge_ne_zero g hg (matrix a b) w σ h n
  have hsrc : (g.toMultiGraph hg).src n=⟨e.1,hv.1⟩ := by
    apply Fin.ext
    exact congrArg Prod.fst hn
  have hdst : (g.toMultiGraph hg).dst n=⟨e.2.1,hv.2.1⟩ := by
    apply Fin.ext
    exact congrArg (fun p : Edge=>p.2.1) hn
  rw [hsrc,hdst] at hz
  simpa only [assignmentSide,dif_pos hv.1,dif_pos hv.2.1] using matrix_crosses a b _ _ hz

theorem partition_zero_of_rejected (g : MixedCode) (hg : g.Valid 1 0)
    (a : Fin k → K) (b : Fin l → K) (w : Fin k ⊕ Fin l → K)
    (h : (coloring g).1≠true) : (g.toMultiGraph hg).partition (matrix a b) w=0 := by
  apply Finset.sum_eq_zero
  intro σ _
  by_contra hz
  exact h ((coloring_complete g).mpr ⟨assignmentSide g σ,nonzero_assignment_proper g hg a b w σ hz⟩)

end PlanarHom.BipartiteRankTwoTractability
