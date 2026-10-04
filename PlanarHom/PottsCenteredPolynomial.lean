import PlanarHom.ProperColoringPottsReduction
import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Tactic.FieldSimp

/-! The literal normalized centered Potts polynomial and exact samples obtained
from ordinary I+J by parallel-edge thickening. This is the algebraic input to
same-q coefficient access; no radial coefficient identity is assumed here. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open MultiGraph Polynomial ProperColoringPottsReduction
variable {V E : Type} [Fintype V] [Fintype E]

def entry (q : ℕ) (i j : Fin q) : Polynomial ℚ :=
  C 1+X*C ((if i=j then (q:ℚ) else 0)-1)

def polynomial (G : MultiGraph V E) (q : ℕ) : Polynomial ℚ :=
  C ((q:ℚ)⁻¹^Fintype.card V)*G.unweighted (entry q)

theorem entry_degree (q : ℕ) (i j : Fin q) : (entry q i j).natDegree≤1 := by
  unfold entry
  exact (natDegree_add_le _ _).trans (max_le (by simp) (by
    apply natDegree_mul_le.trans
    simp only [natDegree_X,natDegree_C,Nat.add_zero,le_refl]))

theorem natDegree_le (G : MultiGraph V E) (q : ℕ) :
    (polynomial G q).natDegree≤Fintype.card E := by
  apply (natDegree_C_mul_le _ _).trans
  rw [unweighted_eq]
  apply natDegree_sum_le_of_forall_le
  intro σ _
  apply (natDegree_prod_le _ _).trans
  calc
    _ ≤ ∑ _e : E,1 := Finset.sum_le_sum (fun e _ => entry_degree q _ _)
    _ = _ := by simp

theorem eval_polynomial (G : MultiGraph V E) (q : ℕ) (x : ℚ) :
    (polynomial G q).eval x=(q:ℚ)⁻¹^Fintype.card V *
      G.unweighted (fun (i j : Fin q) => 1+x*((if i=j then (q:ℚ) else 0)-1)) := by
  simp [polynomial,entry,unweighted_eq,eval_finset_sum,eval_prod]

def sampleNode (q k : ℕ) : ℚ := ((2:ℚ)^k-1)/((2:ℚ)^k+q-1)
def sampleScale (q k : ℕ) : ℚ := (q:ℚ)/((2:ℚ)^k+q-1)

theorem sampleDen_pos (q k : ℕ) (hq : 0<q) : 0<(2:ℚ)^k+q-1 := by
  have hpow : 1≤(2:ℚ)^k := one_le_pow₀ (by norm_num)
  have hqp : (0:ℚ)<q := by exact_mod_cast hq
  linarith

theorem entry_sample (q k : ℕ) (hq : 0<q) (i j : Fin q) :
    1+sampleNode q k*((if i=j then (q:ℚ) else 0)-1)=
      sampleScale q k*(positivePottsMatrix q i j)^k := by
  have hd := (sampleDen_pos q k hq).ne'
  by_cases hij : i=j
  · simp only [if_pos hij,positivePottsMatrix,hij,ite_true,sampleNode,sampleScale]
    field_simp
    ring
  · simp only [if_neg hij,positivePottsMatrix,hij,ite_false,one_pow,sampleNode,sampleScale]
    field_simp
    ring

/-- This is exactly the value of the literal k-parallel source graph, with an
explicit rational normalization and no extra coefficient oracle. -/
theorem eval_sample (G : MultiGraph V E) (q k : ℕ) (hq : 0<q) :
    (polynomial G q).eval (sampleNode q k)=
      (q:ℚ)⁻¹^Fintype.card V*(sampleScale q k)^Fintype.card E*
        G.unweighted (fun i j => (positivePottsMatrix q i j)^k) := by
  rw [eval_polynomial]
  simp_rw [entry_sample q k hq]
  rw [unweighted,partition_scale]
  simp only [unweighted]
  ring

theorem sampleNode_injective (q : ℕ) (hq : 0<q) : Function.Injective (sampleNode q) := by
  intro k l h
  have hdk := (sampleDen_pos q k hq).ne'
  have hdl := (sampleDen_pos q l hq).ne'
  have hq0 : (q:ℚ)≠0 := by exact_mod_cast Nat.ne_of_gt hq
  unfold sampleNode at h
  have hh := (div_eq_div_iff hdk hdl).mp h
  have hp : (2:ℚ)^k=(2:ℚ)^l := by
    apply mul_left_cancel₀ hq0
    nlinarith
  exact (pow_right_injective₀ (show (0:ℚ)<2 by norm_num) (show (2:ℚ)≠1 by norm_num)) hp
end PlanarHom.PottsCentered
