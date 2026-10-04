import PlanarHom.Gadgets
import PlanarHom.RootedSignatureSpan
import PlanarHom.PlanarEmbedding

/-! Rooted occurrence multigraphs and their exact weighted gluing identity.
The root has one background factor after gluing, including when it has loops.
Planarity preservation and algorithms are separate obligations. -/
noncomputable section
open scoped BigOperators
open Classical
namespace PlanarHom
abbrev RootedGraph (V E : Type*) := MultiGraph (PUnit.{1} ⊕ V) E
namespace RootedGraph
local instance (priority := 10000) rootedGadgetsDecEq0 (α : Type*) : DecidableEq α := Classical.decEq α
variable {V W E F C R : Type*} [Fintype V] [Fintype W] [Fintype E] [Fintype F]
variable [Fintype C] [CommSemiring R]

def extend (i : C) (σ : V → C) : PUnit ⊕ V → C := Sum.elim (fun _ => i) σ

def signature (G : RootedGraph V E) (M : Matrix C C R) (w : C → R) : C → R :=
  fun i => ∑ σ : V → C, (∏ v, w (σ v)) *
    ∏ e, M (extend i σ (G.src e)) (extend i σ (G.dst e))

omit [Fintype C] in
theorem assignment_extend (G : RootedGraph V E) (M : Matrix C C R) (w : C → R)
    (i : C) (σ : V → C) :
    G.assignmentWeight M w (extend i σ) = w i *
      ((∏ v, w (σ v)) * ∏ e, M (extend i σ (G.src e)) (extend i σ (G.dst e))) := by
  simp [MultiGraph.assignmentWeight, extend, Fintype.prod_sum_type, mul_assoc]

theorem partition_eq_sum_signature (G : RootedGraph V E) (M : Matrix C C R) (w : C → R) :
    G.partition M w = ∑ i, w i * signature G M w i := by
  unfold MultiGraph.partition
  rw [TwoTerminal.sum_colorings_sum]
  calc
    (∑ σ : PUnit → C, ∑ τ : V → C, G.assignmentWeight M w (Sum.elim σ τ)) =
        ∑ i : C, ∑ τ : V → C, G.assignmentWeight M w (extend i τ) := by
      apply Fintype.sum_equiv (Equiv.funUnique PUnit C)
      intro σ
      apply Finset.sum_congr rfl
      intro τ _
      congr 1
    _ = _ := by simp only [assignment_extend, signature, Finset.mul_sum]

def glue (G : RootedGraph V E) (H : RootedGraph W F) : RootedGraph (V ⊕ W) (E ⊕ F) where
  src := Sum.elim (fun e => Sum.map id Sum.inl (G.src e))
    (fun f => Sum.map id Sum.inr (H.src f))
  dst := Sum.elim (fun e => Sum.map id Sum.inl (G.dst e))
    (fun f => Sum.map id Sum.inr (H.dst f))

omit [Fintype V] [Fintype W] [Fintype C] in
@[simp] theorem extend_glue_left (i : C) (σ : V → C) (τ : W → C) (v : PUnit ⊕ V) :
    extend i (Sum.elim σ τ) (Sum.map id Sum.inl v) = extend i σ v := by cases v <;> rfl
omit [Fintype V] [Fintype W] [Fintype C] in
@[simp] theorem extend_glue_right (i : C) (σ : V → C) (τ : W → C) (v : PUnit ⊕ W) :
    extend i (Sum.elim σ τ) (Sum.map id Sum.inr v) = extend i τ v := by cases v <;> rfl

theorem signature_glue (G : RootedGraph V E) (H : RootedGraph W F)
    (M : Matrix C C R) (w : C → R) (i : C) :
    signature (glue G H) M w i = signature G M w i * signature H M w i := by
  unfold signature
  rw [TwoTerminal.sum_colorings_sum]
  simp only [Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, glue,
    extend_glue_left, extend_glue_right, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  apply Finset.sum_congr rfl
  intro σ _
  ac_rfl

theorem partition_glue (G : RootedGraph V E) (H : RootedGraph W F)
    (M : Matrix C C R) (w : C → R) :
    (glue G H).partition M w = ∑ i, w i * signature G M w i * signature H M w i := by
  rw [partition_eq_sum_signature]
  simp only [signature_glue, mul_assoc]

/-- The original root-domain restriction; every vertex weight, including the
root, remains present. -/
def restricted (G : RootedGraph V E) (M : Matrix C C R) (w : C → R) (X : Set C) : R :=
  ∑ i, if i ∈ X then w i * signature G M w i else 0

end RootedGraph

/-- A single set of every finite rooted planar incidence presentation. -/
def FiniteRootedPlanar := Σ n m : ℕ, {G : RootedGraph (Fin n) (Fin m) // G.Planar}

namespace FiniteRootedPlanar
variable {K C : Type*} [Fintype C]

def signature [CommSemiring K] (G : FiniteRootedPlanar) (M : Matrix C C K) (w : C → K) : C → K :=
  RootedGraph.signature G.2.2.val M w

def gluedValue [CommSemiring K] (G H : FiniteRootedPlanar) (M : Matrix C C K) (w : C → K) : K :=
  (RootedGraph.glue G.2.2.val H.2.2.val).partition M w

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The exact fixed-field linear combination in source3.5. Gluing planarity and
its encoded query machine are not asserted by this algebraic theorem. -/
theorem exists_root_restriction_coefficients (M : Matrix C C K) (w : C → K)
    (hw : ∀ i, 0 < w i) (X : Set C) :
    ∃ n : ℕ, ∃ graphs : Fin n → FiniteRootedPlanar, ∃ c : Fin n → K,
      ∀ G : FiniteRootedPlanar,
        RootedGraph.restricted G.2.2.val M w X = ∑ j, c j * gluedValue (graphs j) G M w := by
  obtain ⟨n,graphs,c,h⟩ := RootedSignatureSpan.exists_family_coefficients w hw
    (fun G : FiniteRootedPlanar => signature G M w) (fun i => if i ∈ X then 1 else 0)
  refine ⟨n,graphs,c,?_⟩
  intro G
  simpa [RootedSignatureSpan.pairing, RootedGraph.restricted, gluedValue,
    RootedGraph.partition_glue, signature, mul_ite, ite_mul] using h G

end FiniteRootedPlanar
end PlanarHom
