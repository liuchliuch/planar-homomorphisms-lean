import PlanarHom.BooleanInnerRecoveryCorrectness
import Mathlib.Algebra.Polynomial.BigOperators

/-! NEW polynomial for the literal retained tensor evaluation. The degree counts
actual selected occurrences, including loops and repeated edges. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanRetentionPolynomial
open Complexity Complexity.MixedCode BooleanTensorSpectral BooleanTensorPartitionMoments
open BooleanSpectralCounts Polynomial
variable {K : Type} [Field K] [Algebra ℚ K] {b d bt ut : ℕ}

def matrix (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) :
    Matrix (Fin d→Bool) (Fin d→Bool) (Polynomial K) :=
  tensor (fun i=>if cls i=g0 then block (C (c (cls i))) (C (a (cls i)))
    (C (w (cls i))*X) else 1)

theorem eval_matrix (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (x : K) :
    (matrix cls c a w g0).map (evalRingHom x) =
      tensor (fun i=>if cls i=g0 then block (c (cls i)) (a (cls i)) (w (cls i)*x) else 1) := by
  rw [matrix,BooleanTensorRingMap.tensor_map]
  congr 1
  funext i
  by_cases hi:cls i=g0
  · simp only [hi,if_true]
    rw [BooleanTensorRingMap.block_map]
    simp
  · simp [hi]

theorem block_degree (c a w : K) (i j : Bool) :
    (block (C c) (C a) (C w*X) i j).natDegree ≤ 1 := by
  cases i <;> cases j <;>
    simp [block,traceless,Matrix.add_apply,Matrix.smul_apply] <;>
    first | exact natDegree_mul_le.trans (by simp) |
      exact natDegree_add_le.trans (by simp) |
      exact natDegree_sub_le.trans (by simp)

theorem matrix_degree (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b)
    (i j : Fin d→Bool) : (matrix cls c a w g0 i j).natDegree ≤ multiplicity cls g0 := by
  unfold matrix tensor
  refine (natDegree_prod_le _ _).trans ?_
  calc
    _ ≤ ∑ k : Fin d, if cls k=g0 then 1 else 0 := by
      apply Finset.sum_le_sum
      intro k _
      by_cases hk:cls k=g0
      · simpa only [hk,if_true] using block_degree (c (cls k)) (a (cls k)) (w (cls k)) (i k) (j k)
      · by_cases hij:i k=j k <;> simp [hk,Matrix.one_apply,hij]
    _ = multiplicity cls g0 := by simp [BooleanSpectralCounts.multiplicity,Finset.sum_boole]

def partition (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) :
    Polynomial K :=
  ∑ σ : Fin g.vertices→Fin d→Bool,
    C (binaryRemainder g selected.val M U ω σ) *
      ((selectedBinaryColors g hg selected σ).map (fun p=>matrix cls c a w g0 p.1 p.2)).prod

theorem eval_partition (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) (x : K) :
    (partition g hg selected M U ω cls c a w g0).eval x =
    g.evaluate hg (replace M selected
      (tensor (fun i=>if cls i=g0 then block (c (cls i)) (a (cls i)) (w (cls i)*x) else 1))) U ω := by
  rw [partition,eval_finset_sum,evaluate_eq_binary_product_sum _ hg selected.val]
  apply Finset.sum_congr rfl
  intro σ _
  rw [binaryRemainder_congr g selected.val M (replace M selected
    (tensor (fun i=>if cls i=g0 then block (c (cls i)) (a (cls i)) (w (cls i)*x) else 1))) U ω (fun l hl=>by
    simp only [replace,if_neg (fun h=>hl (congrArg Fin.val h))])]
  rw [← selectedBinaryColors_product g hg selected]
  simp only [eval_mul,eval_C,eval_list_prod,List.map_map,Function.comp_apply]
  apply congrArg (fun z=>binaryRemainder g selected.val M U ω σ * z)
  apply congrArg List.prod
  apply List.map_congr_left
  intro p _
  have h:=congrFun (congrFun (eval_matrix cls c a w g0 x) p.1) p.2
  simpa [replace,Matrix.map_apply] using h

theorem partition_degree (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (ω : (Fin d→Bool)→K) (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b) :
    (partition g hg selected M U ω cls c a w g0).natDegree ≤
      multiplicity cls g0 * g.markedCount selected.val := by
  apply natDegree_sum_le_of_forall_le
  intro σ _
  refine natDegree_mul_le.trans ?_
  simp only [natDegree_C,zero_add]
  refine (natDegree_list_prod_le _).trans ?_
  rw [List.map_map]
  calc
    _ ≤ (selectedBinaryColors g hg selected σ).length * multiplicity cls g0 := by
      simpa only [List.length_map,smul_eq_mul] using
        List.sum_le_card_nsmul
          ((selectedBinaryColors g hg selected σ).map
            (fun p=>(matrix cls c a w g0 p.1 p.2).natDegree))
          (multiplicity cls g0) (by
            intro n hn
            obtain ⟨p,_,rfl⟩:=List.mem_map.mp hn
            exact matrix_degree cls c a w g0 p.1 p.2)
    _ = _ := by rw [selectedBinaryColors_length,Nat.mul_comm]

end PlanarHom.BooleanRetentionPolynomial
