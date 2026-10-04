import PlanarHom.SignedNandExactOneClause
import Mathlib.Algebra.BigOperators.Pi

/-! Exact global signed partition identity for an arbitrary positive-exact-one
formula. Every clause contributes a literal triangle and one fresh marked
center, retaining edge occurrences even when a formula repeats a variable. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SignedNandFormulaIdentity
open MultiGraph ParsimoniousNorOneInThree SignedNandExactOneClause

variable {V C : Type} [Fintype V] [Fintype C]

def graph (port : C → Fin 3 → V) : MultiGraph (V ⊕ C) (C × Fin 6) where
  src e := ![Sum.inl (port e.1 0),Sum.inl (port e.1 1),Sum.inl (port e.1 2),
    Sum.inl (port e.1 0),Sum.inl (port e.1 1),Sum.inl (port e.1 2)] e.2
  dst e := ![Sum.inl (port e.1 1),Sum.inl (port e.1 2),Sum.inl (port e.1 0),
    Sum.inr e.1,Sum.inr e.1,Sum.inr e.1] e.2

def Satisfies (port : C → Fin 3 → V) (b : V → Bool) : Prop :=
  ∀ c,ExactlyOne (b (port c 0)) (b (port c 1)) (b (port c 2))

def count (port : C → Fin 3 → V) : ℕ := Fintype.card {b : V → Bool // Satisfies port b}

variable {R : Type*} [CommRing R]

/-- Literal NAND edge product and activity -1 at exactly the fresh centers. -/
def weight (port : C → Fin 3 → V) (col : V ⊕ C → Bool) : R :=
  (∏ e : C × Fin 6,nandWeight (col ((graph port).src e)) (col ((graph port).dst e))) *
    ∏ c : C,centerActivity (col (Sum.inr c))

def partition (port : C → Fin 3 → V) : R := ∑ col : V ⊕ C → Bool,weight port col

theorem weight_glue (port : C → Fin 3 → V) (b : V → Bool) (t : C → Bool) :
    weight (R:=R) port (Sum.elim b t)=
      ∏ c,term (extension (b (port c 0)) (b (port c 1)) (b (port c 2)) (t c)) := by
  unfold weight
  rw [Fintype.prod_prod_type,← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro c _
  simp [graph,term_eq,Fin.prod_univ_succ]
  ring

/-- Summing every fresh center gives precisely the formula indicator, with no
multiplicity factor and no requirement that the formula have distinct ports. -/
theorem sum_centers (port : C → Fin 3 → V) (b : V → Bool) :
    (∑ t : C → Bool,weight (R:=R) port (Sum.elim b t))=
      if Satisfies port b then 1 else 0 := by
  simp_rw [weight_glue]
  rw [← Fintype.prod_sum (fun (c : C) (t : Bool) =>
    term (R:=R) (extension (b (port c 0)) (b (port c 1)) (b (port c 2)) t))]
  simp_rw [center_sum]
  by_cases h : Satisfies port b
  · rw [if_pos h]
    apply Finset.prod_eq_one
    intro c _
    exact if_pos (h c)
  · rw [if_neg h]
    obtain ⟨c,hc⟩ := not_forall.mp h
    apply Finset.prod_eq_zero (Finset.mem_univ c)
    exact if_neg hc

/-- The full materialized graph partition is exactly the number of satisfying
Boolean assignments, including empty formulas, isolated variables and repeats.
Planarity is a separate geometric construction and is not assumed by this law. -/
theorem partition_eq_count (port : C → Fin 3 → V) :
    partition (R:=R) port=(count port : R) := by
  unfold partition
  rw [Fintype.sum_equiv (Equiv.sumArrowEquivProdArrow V C Bool)
    (weight port) (fun p => weight port (Sum.elim p.1 p.2)) (by
      intro col
      congr 1
      funext v
      cases v <;> rfl)]
  rw [Fintype.sum_prod_type]
  simp_rw [sum_centers]
  rw [Finset.sum_boole]
  simp [count,Fintype.card_subtype]
end PlanarHom.SignedNandFormulaIdentity
