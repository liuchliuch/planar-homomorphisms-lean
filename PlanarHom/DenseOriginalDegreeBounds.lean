import PlanarHom.DensePolynomialBoxDegree
import PlanarHom.CoefficientConvolutionAlgebra
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! NEW bounds for original dense inputs and their genuine products/minors.
The grid degree is computed from literal input bit length, never supplied as
an unchecked degree or height certificate. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity ListFlattenMachines

 theorem codeLength_member {A:Type} (e:BitEncoding A) {xs:List A} {x:A} (hx:x∈xs) :
    (e.encode x).length≤(e.list.encode xs).length := by
  have hs:=List.single_le_sum (l:=xs.map (fun a=>(e.encode a).length))
    (fun y _=>Nat.zero_le y) (e.encode x).length (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hp:=payloadSize_le_word e xs
  rw [payloadSize_eq] at hp
  omega

 theorem code_box_degree (n:ℕ) (p:Code n) :
    BoxDegree n ((encoding n).encode p).length (interpret n p) := by
  induction n with
  | zero=>trivial
  | succ n ih=>
    refine ⟨?_,?_⟩
    · exact (CoefficientListAlgebra.polynomial_natDegree_le _).trans
        (by simpa only [List.length_map] using BitEncoding.list_length_le (encoding n) p)
    · intro k
      rw [interpret_coeff]
      cases he:p[k]? with
      | none=>simpa only [he,Option.getD_none,interpret_zero] using boxDegree_zero n ((encoding (n+1)).encode p).length
      | some a=>
        simp only [he,Option.getD_some]
        exact boxDegree_mono n (codeLength_member (encoding n) (List.mem_of_getElem? he)) (ih a)

 theorem boxDegree_lookup (n:ℕ) (xs:List (Code n)) (k:ℕ) :
    BoxDegree n ((encoding n).list.encode xs).length (interpret n (xs[k]?.getD (zero n))) := by
  cases he:xs[k]? with
  | none=>simpa only [he,Option.getD_none,interpret_zero] using boxDegree_zero n ((encoding n).list.encode xs).length
  | some a=>
    simp only [he,Option.getD_some]
    exact boxDegree_mono n (codeLength_member (encoding n) (List.mem_of_getElem? he)) (code_box_degree n a)

 theorem boxDegree_prod (n d:ℕ) {I:Type*} (s:Finset I) (P:I→Poly n)
    (h:∀i∈s,BoxDegree n d (P i)) : BoxDegree n (s.card*d) (∏i∈s,P i) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simpa using boxDegree_one n 0
  | @insert i s hi ih=>
    rw [Finset.prod_insert hi,Finset.card_insert_of_notMem hi]
    have ht:=boxDegree_mul n (h i (Finset.mem_insert_self _ _))
      (ih (fun j hj=>h j (Finset.mem_insert_of_mem hj)))
    simpa only [Nat.add_mul,Nat.one_mul,Nat.add_comm] using ht

 theorem boxDegree_list_prod (n d:ℕ) (ps:List (Poly n)) (h:∀p∈ps,BoxDegree n d p) :
    BoxDegree n (ps.length*d) ps.prod := by
  induction ps with
  | nil=>simpa using boxDegree_one n 0
  | cons p ps ih=>
    have hh:=boxDegree_mul n (h p (by simp)) (ih (fun q hq=>h q (by simp [hq])))
    simpa only [List.length_cons,List.prod_cons,Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

 theorem boxDegree_intCast (n d:ℕ) (z:ℤ) : BoxDegree n d (z:Poly n) := by
  simpa only [map_intCast] using boxDegree_qHom n d (z:ℚ)

 theorem boxDegree_determinant (n d:ℕ) {I:Type*} [Fintype I] [DecidableEq I]
    (A:Matrix I I (Poly n)) (hA:∀i j,BoxDegree n d (A i j)) :
    BoxDegree n (Fintype.card I*d) A.det := by
  rw [Matrix.det_apply]
  apply boxDegree_sum
  intro σ hσ
  have hp:=boxDegree_prod n d Finset.univ (fun i=>A (σ i) i) (fun i _=>hA _ _)
  have hs:=boxDegree_mul n (boxDegree_intCast n 0 (Equiv.Perm.sign σ:ℤ)) hp
  simpa only [zero_add,Finset.card_univ,Units.smul_def,zsmul_eq_mul] using hs

 theorem product_input_degree (n:ℕ) (ps:List (Code n)) :
    BoxDegree n (((encoding n).list.encode ps).length^2) ((ps.map (interpret n)).prod) := by
  have hh:=boxDegree_list_prod n ((encoding n).list.encode ps).length (ps.map (interpret n)) (by
    intro p hp
    obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
    exact boxDegree_mono n (codeLength_member (encoding n) ha) (code_box_degree n a))
  apply boxDegree_mono n _ hh
  simp only [List.length_map,pow_two]
  exact Nat.mul_le_mul_right _ (BitEncoding.list_length_le (encoding n) ps)

end PlanarHom.DensePolynomial
