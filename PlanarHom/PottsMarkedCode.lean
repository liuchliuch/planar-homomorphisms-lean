import PlanarHom.PottsMarkedCoefficientFilter
import PlanarHom.PottsCenteredStretchIdentity
import PlanarHom.MixedRelabelSemantics
import PlanarHom.SelectedStretchMachines

/-! NEW reconstruction: a materialized two-label graph is converted to an
ordinary one-label coefficient query. Long occurrences receive private paths,
all labels are then physically erased by the proved relabeling machine. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.PottsCentered
open Complexity Complexity.MixedCode FiniteLabelLookupMachines

def longPositions (g : MixedCode) : Finset (Fin g.edges.length) :=
  Finset.univ.filter (fun e => (g.edges.get e).2.2=0)

def stretchedCode (g : MixedCode) (n : ℕ) : MixedCode :=
  (g.stretchLabel 0 0 n).relabelBinary (finTable (fun _ : Fin 2 => (0 : Fin 1)))

theorem stretchedCode_valid (g : MixedCode) (hg : g.Valid 2 0) (n : ℕ) :
    (stretchedCode g n).Valid 1 0 :=
  relabelBinary_valid _ (g.stretchLabel_valid hg 0 0 n (by decide) (keepShort hg))
    (lookup_finTable_lt (fun _ : Fin 2 => (0 : Fin 1)))

theorem stretchedCode_planar (g : MixedCode) (hg : g.PlanarValid 2 0) (n : ℕ) :
    (stretchedCode g n).PlanarValid 1 0 :=
  relabelBinary_planar _ (g.stretchLabel_planar hg 0 0 n (by decide) (keepShort hg.1))
    (lookup_finTable_lt (fun _ : Fin 2 => (0 : Fin 1)))

/-- The runtime path length is unary and every fresh vertex/edge is emitted. -/
theorem fp_stretchedCode : FP (BitEncoding.unaryNat.prod MixedCode.encoding) MixedCode.encoding
    (fun p => stretchedCode p.2 p.1) :=
  (MixedCode.fp_stretchLabel 0 0).comp
    (fp_relabelBinary (finTable (fun _ : Fin 2 => (0 : Fin 1))))

private theorem unary_nil (g : MixedCode) (hg : g.Valid 2 0) : g.unaries=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  exact Nat.not_lt_zero _ (hg.2 u hu).2

theorem eval_markedPolynomial_code (g : MixedCode) (hg : g.Valid 2 0)
    (q N : ℕ) (x : ℚ) :
    (markedPolynomial (g.toMultiGraph hg) q (longPositions g) N).eval x=
      (q:ℚ)⁻¹^g.vertices*g.evaluate hg (twoLabelEntries q (x^N) x)
        (fun u : Fin 0 => u.elim0) (fun _ => 1) := by
  simp only [markedPolynomial,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_finset_sum,
    Polynomial.eval_prod,Polynomial.eval_add,Polynomial.eval_one,Polynomial.eval_pow,Polynomial.eval_X,
    Fintype.card_fin]
  congr 1
  unfold evaluate
  rw [unary_nil g hg]
  simp only [Finset.prod_const_one,one_mul,List.map_nil,List.prod_nil,mul_one]
  apply Finset.sum_congr (by ext σ; simp)
  intro σ _
  rw [prod_map_get]
  apply Finset.prod_congr rfl
  intro e _
  have hv := hg.1 (g.edges.get e) (List.get_mem _ _)
  simp only [binaryValue,dif_pos hv,twoLabelEntries,toMultiGraph,longPositions,
    Finset.mem_filter,Finset.mem_univ,true_and]
  split_ifs <;> simp [entryMatrix_apply,pow_one]

/-- Exact polynomial identity for the actual one-label numeric output. This
includes its normalization by the actual output vertex header. -/
theorem stretchedCode_polynomial (g : MixedCode) (hg : g.Valid 2 0) (q n : ℕ) (hq : 0<q) :
    polynomial ((stretchedCode g n).toMultiGraph (stretchedCode_valid g hg n)) q=
      markedPolynomial (g.toMultiGraph hg) q (longPositions g) (n+1) := by
  apply Polynomial.funext
  intro x
  rw [eval_markedPolynomial_code]
  have hr := evaluate_relabelBinary (g.stretchLabel 0 0 n)
    (g.stretchLabel_valid hg 0 0 n (by decide) (keepShort hg))
    (fun _ : Fin 2 => (0 : Fin 1)) (fun _ : Fin 1 => entryMatrix q x)
    (fun u : Fin 0 => u.elim0) (fun _ => 1)
  rw [evaluate_homogeneous] at hr
  simp only [Function.comp_def] at hr
  have hn := normalized_stretch_evaluation g hg q n hq x
  rw [← hr] at hn
  simpa only [eval_polynomial,entryMatrix_apply,interaction,stretchedCode,relabelBinary,
    Fintype.card_fin,MultiGraph.unweighted] using hn

/-- The actual ordinary coefficient query selects all long occurrences and
exactly d short occurrences. No semantic or polynomial-time gate is assumed. -/
theorem stretchedCode_coefficient_filter (g : MixedCode) (hg : g.Valid 2 0)
    (q n d : ℕ) (hq : 0<q) (hn : (Finset.univ\longPositions g).card<n+1) :
    (polynomial ((stretchedCode g n).toMultiGraph (stretchedCode_valid g hg n)) q).coeff
      ((n+1)*(longPositions g).card+d)=
      ∑ A : Finset (Fin g.edges.length),
        if longPositions g⊆A ∧ (A\longPositions g).card=d
        then selectedValue (g.toMultiGraph hg) q A else 0 := by
  rw [stretchedCode_polynomial g hg q n hq]
  have hi : instDecidableEqFin g.edges.length=Classical.decEq (Fin g.edges.length) := Subsingleton.elim _ _
  rw [hi] at hn ⊢
  exact marked_coefficient_filter (g.toMultiGraph hg) q (longPositions g) (n+1) d hn
end PlanarHom.PottsCentered
