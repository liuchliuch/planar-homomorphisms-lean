import PlanarHom.DenseDenominatorClearing
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! NEW variable-order Cramer solver for polynomial matrices, returning concrete
noncanonical fraction pairs. Every determinant is the actual grid machine. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 def replaceColumn (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) (k:ℕ) : List (List (Code n)) :=
    (List.range g.length).map (fun i=>(List.range g.length).map (fun j=>
      if j=k then b[i]?.getD (zero n) else matrixEntry n g i j))

 def solvePolynomial (n:ℕ) (p:List (List (Code n))×List (Code n)) : List (FractionCode n) :=
    (List.range p.1.length).map (fun k=>
      (determinantGrid n (replaceColumn n p.1 p.2 k),determinantGrid n p.1))

 def rhsValue (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) : Fin g.length→Poly n :=
    fun i=>interpret n (b[i.val]?.getD (zero n))

 theorem replaceColumn_ofFn (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) (k:Fin g.length) :
    replaceColumn n g b k.val=List.ofFn (fun i:Fin g.length=>List.ofFn (fun j:Fin g.length=>
      if j=k then b[i.val]?.getD (zero n) else matrixEntry n g i.val j.val)) := by
  simp only [replaceColumn,VariableDeterminant.range_map_eq_ofFn]
  congr 1
  funext i
  congr 1
  funext j
  simp only [Fin.ext_iff]

 theorem matrixValue_ofFn (n m:ℕ) (A:Fin m→Fin m→Code n) :
    matrixValue n (List.ofFn (fun i=>List.ofFn (A i)))=
      fun i j=>interpret n (A (Fin.cast (by simp) i) (Fin.cast (by simp) j)) := by
  ext i j
  have hi:i.val<m:=by simpa using i.isLt
  have hj:j.val<m:=by simpa using j.isLt
  simp only [matrixValue,matrixEntry,List.getElem?_ofFn,hi,hj,dif_pos,Option.getD_some]
  rfl

 theorem determinantGrid_ofFn (n m:ℕ) (A:Fin m→Fin m→Code n) :
    interpret n (determinantGrid n (List.ofFn (fun i=>List.ofFn (A i))))=
      (show Matrix (Fin m) (Fin m) (Poly n) from fun i j=>interpret n (A i j)).det := by
  rw [determinantGrid_eq,matrixValue_ofFn]
  exact Matrix.det_submatrix_equiv_self (finCongr (by simp : (List.ofFn (fun i=>List.ofFn (A i))).length=m))
    (show Matrix (Fin m) (Fin m) (Poly n) from fun i j=>interpret n (A i j))

 theorem replaced_determinant (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) (k:Fin g.length) :
    interpret n (determinantGrid n (replaceColumn n g b k.val))=
      ((matrixValue n g).updateCol k (rhsValue n g b)).det := by
  rw [replaceColumn_ofFn,determinantGrid_ofFn]
  apply congrArg Matrix.det
  ext i j
  by_cases h:j=k <;> simp [h,Matrix.updateCol_apply,matrixValue,rhsValue]

 theorem solvePolynomial_length (n:ℕ) (p:List (List (Code n))×List (Code n)) :
    (solvePolynomial n p).length=p.1.length := by simp [solvePolynomial]

 theorem solvePolynomial_get (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) (k:Fin g.length) :
    (solvePolynomial n (g,b))[k.val]?.getD (fractionZero n)=
      (determinantGrid n (replaceColumn n g b k.val),determinantGrid n g) := by
  simp only [solvePolynomial,List.getElem?_map,List.getElem?_range k.isLt,Option.map_some,Option.getD_some]

 theorem solvePolynomial_valid (n:ℕ) (g:List (List (Code n))) (b:List (Code n))
    (h:(matrixValue n g).det≠0) (k:Fin g.length) :
    FractionValid n ((solvePolynomial n (g,b))[k.val]?.getD (fractionZero n)) := by
  rw [solvePolynomial_get]
  change interpret n (determinantGrid n g)≠0
  rwa [determinantGrid_eq]

 theorem solvePolynomial_value (n:ℕ) (g:List (List (Code n))) (b:List (Code n)) (k:Fin g.length) :
    fractionValue n ((solvePolynomial n (g,b))[k.val]?.getD (fractionZero n))=
      ((matrixValue n g).map (algebraMap (Poly n) (RationalFunction n))).cramer
        (fun i=>algebraMap (Poly n) (RationalFunction n) (rhsValue n g b i)) k /
      ((matrixValue n g).map (algebraMap (Poly n) (RationalFunction n))).det := by
  rw [solvePolynomial_get,fractionValue,replaced_determinant,determinantGrid_eq,
    RingHom.map_det,RingHom.map_det,Matrix.cramer_apply]
  congr 2
  ext i j
  by_cases h:j=k <;> simp [h,Matrix.map_apply,Matrix.updateCol_apply]

 theorem solvePolynomial_correct (n:ℕ) (g:List (List (Code n))) (b:List (Code n))
    (h:(matrixValue n g).det≠0) :
    ((matrixValue n g).map (algebraMap (Poly n) (RationalFunction n))).mulVec
      (fun k=>fractionValue n ((solvePolynomial n (g,b))[k.val]?.getD (fractionZero n)))=
        fun i=>algebraMap (Poly n) (RationalFunction n) (rhsValue n g b i) := by
  let A:=(matrixValue n g).map (algebraMap (Poly n) (RationalFunction n))
  let v:=fun i=>algebraMap (Poly n) (RationalFunction n) (rhsValue n g b i)
  have hd:A.det≠0 := by
    intro hz
    have hm:=RingHom.map_det (algebraMap (Poly n) (RationalFunction n)) (matrixValue n g)
    have hz':algebraMap (Poly n) (RationalFunction n) (matrixValue n g).det=0:=hm.trans hz
    exact h ((IsFractionRing.to_map_eq_zero_iff).mp hz')
  have he:(fun k=>fractionValue n ((solvePolynomial n (g,b))[k.val]?.getD (fractionZero n)))=
      A.det⁻¹ • A.cramer v := by
    funext k
    rw [solvePolynomial_value]
    simp only [A,v,Pi.smul_apply,smul_eq_mul,div_eq_mul_inv,mul_comm]
  rw [he,Matrix.mulVec_smul,Matrix.mulVec_cramer,smul_smul,inv_mul_cancel₀ hd,one_smul]

 theorem fp_replaceColumn (n:ℕ) :
    FP (((encoding n).list.list.prod (encoding n).list).prod BitEncoding.nat)
      (encoding n).list.list (fun p=>replaceColumn n p.1.1 p.1.2 p.2) := by
  let e:=encoding n
  let ep:=e.list.list.prod e.list
  let ec:=ep.prod BitEncoding.nat
  let ei:=ec.prod BitEncoding.nat
  have hg:=(fp_fst ep BitEncoding.nat).comp (fp_fst e.list.list e.list)
  have hb:=(fp_fst ep BitEncoding.nat).comp (fp_snd e.list.list e.list)
  have hk:=fp_snd ep BitEncoding.nat
  have hr:=(hg.comp (ListUnaryLengthMachine.fp_length e.list)).comp UnaryArithmeticMachines.fp_range
  have hp:=fp_fst ei BitEncoding.nat
  have hc:=hp.comp (fp_fst ec BitEncoding.nat)
  have hi:=hp.comp (fp_snd ec BitEncoding.nat)
  have hj:=fp_snd ei BitEncoding.nat
  have he:=(hj.pair (hc.comp hk)).comp NatListSumMachines.fp_equal
  have hv:=(hi.pair (hc.comp hb)).comp (fp_codeLookup e (zero n))
  have ha:=((hc.comp hg).pair (hi.pair hj)).comp (fp_matrixEntry n)
  have hf:=he.ite hv ha
  have inner:=(((fp_id ei).pair ((fp_fst ec BitEncoding.nat).comp hr)).comp
    (ListContextMachines.fp_mapWithContext ei BitEncoding.nat e _ hf))
  exact (((fp_id ec).pair hr).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat e.list _ inner)).congr
      (fun _=>by simp only [replaceColumn,Function.comp_def,id_eq])

 theorem fp_solvePolynomial (n:ℕ) :
    FP ((encoding n).list.list.prod (encoding n).list) (fractionEncoding n).list (solvePolynomial n) := by
  let e:=encoding n
  let ep:=e.list.list.prod e.list
  have hg:=fp_fst e.list.list e.list
  have hr:=(hg.comp (ListUnaryLengthMachine.fp_length e.list)).comp UnaryArithmeticMachines.fp_range
  have hn:=(fp_replaceColumn n).comp (fp_determinantGrid n)
  have hd:=((fp_fst ep BitEncoding.nat).comp hg).comp (fp_determinantGrid n)
  exact (((fp_id ep).pair hr).comp
    (ListContextMachines.fp_mapWithContext ep BitEncoding.nat (fractionEncoding n) _ (hn.pair hd)))

end PlanarHom.DensePolynomial
