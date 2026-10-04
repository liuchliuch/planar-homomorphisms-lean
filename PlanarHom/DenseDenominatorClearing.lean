import PlanarHom.DensePolynomialDeterminantGrid

/-! NEW concrete denominator clearing. The common product and each omitted-factor
product use the proved dense grid product machine, with complete polynomial bit
bounds inherited from actual FP composition. No symbolic fraction fold occurs. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 def constant : (n:ℕ)→ℚ→Code n
  | 0,q=>q
  | n+1,q=>[constant n q]

 theorem interpret_constant (n:ℕ) (q:ℚ) : interpret n (constant n q)=qHom n q := by
  induction n with
  | zero=>rfl
  | succ n ih=>
    simp only [interpret,constant,List.map_cons,List.map_nil,CoefficientListAlgebra.polynomial,ih,mul_zero,add_zero]
    rfl

 def fractionZero (n:ℕ) : FractionCode n := (zero n,constant n 1)

 @[simp] theorem fractionZero_valid (n:ℕ) : FractionValid n (fractionZero n) := by
  simp [FractionValid,fractionZero,interpret_constant]
 @[simp] theorem fractionZero_value (n:ℕ) : fractionValue n (fractionZero n)=0 := by
  simp [fractionValue,fractionZero]

 def otherDenominators (n:ℕ) (xs:List (FractionCode n)) (k:ℕ) : List (Code n) :=
    xs.zipIdx.map (fun p=>if p.2=k then constant n 1 else p.1.2)
 def commonDenominator (n:ℕ) (xs:List (FractionCode n)) : Code n :=
    productGrid n (xs.map Prod.snd)
 def clearNumerator (n:ℕ) (xs:List (FractionCode n)) (k:ℕ) : Code n :=
    mul n ((xs[k]?.getD (fractionZero n)).1) (productGrid n (otherDenominators n xs k))

 theorem zipIdx_ofFn {A:Type} {m:ℕ} (xs:Fin m→A) :
    (List.ofFn xs).zipIdx=List.ofFn (fun j:Fin m=>(xs j,j.val)) := by
  apply List.ext_getElem (by simp)
  intro i hi hj
  simp only [List.getElem_zipIdx,List.getElem_ofFn,Nat.zero_add]

 theorem commonDenominator_ofFn (n:ℕ) {m:ℕ} (xs:Fin m→FractionCode n) :
    interpret n (commonDenominator n (List.ofFn xs))=∏j,interpret n (xs j).2 := by
  rw [commonDenominator,productGrid_eq]
  simp only [List.map_ofFn,List.map_map,Function.comp_def,List.prod_ofFn]

 theorem clearNumerator_ofFn (n:ℕ) {m:ℕ} (xs:Fin m→FractionCode n) (k:Fin m) :
    interpret n (clearNumerator n (List.ofFn xs) k.val)=
      interpret n (xs k).1 * ∏j∈Finset.univ.erase k,interpret n (xs j).2 := by
  rw [clearNumerator,interpret_mul,productGrid_eq,otherDenominators,zipIdx_ofFn]
  simp only [List.getElem?_ofFn,k.isLt,Option.getD_some,List.map_ofFn,List.map_map,
    Function.comp_def,List.prod_ofFn]
  congr 1
  have he:∀j:Fin m,(j.val=k.val)↔j=k:=fun _=>Fin.ext_iff.symm
  simp only [he,apply_ite,interpret_constant,map_one]
  rw [←Finset.prod_erase_mul _ _ (Finset.mem_univ k)]
  simp only [ite_true,mul_one]
  apply Finset.prod_congr rfl
  intro j hj
  rw [if_neg (Finset.mem_erase.mp hj).1]

 theorem commonDenominator_valid (n:ℕ) (xs:List (FractionCode n))
    (h:∀x∈xs,FractionValid n x) : interpret n (commonDenominator n xs)≠0 := by
  rw [commonDenominator,productGrid_eq]
  apply List.prod_ne_zero
  intro ha
  obtain ⟨x,hx,hz⟩:=List.mem_map.mp ha
  obtain ⟨y,hy,rfl⟩:=List.mem_map.mp hx
  exact h y hy hz

 theorem clearNumerator_value (n:ℕ) {m:ℕ} (xs:Fin m→FractionCode n) (k:Fin m)
    (h:FractionValid n (xs k)) :
    algebraMap (Poly n) (RationalFunction n) (interpret n (clearNumerator n (List.ofFn xs) k.val))=
      algebraMap (Poly n) (RationalFunction n) (interpret n (commonDenominator n (List.ofFn xs))) *
        fractionValue n (xs k) := by
  rw [clearNumerator_ofFn,commonDenominator_ofFn]
  rw [←Finset.mul_prod_erase _ _ (Finset.mem_univ k)]
  simp only [map_mul,fractionValue]
  have hn:=denominator_ne_zero n (xs k) h
  field_simp

 theorem fp_otherDenominators (n:ℕ) : FP (BitEncoding.nat.prod (fractionEncoding n).list)
    (encoding n).list (fun p=>otherDenominators n p.2 p.1) := by
  let e:=encoding n
  let f:=fractionEncoding n
  have hp:=fp_snd BitEncoding.nat (f.prod BitEncoding.nat)
  have he:=((hp.comp (fp_snd f BitEncoding.nat)).pair
    (fp_fst BitEncoding.nat (f.prod BitEncoding.nat))).comp NatListSumMachines.fp_equal
  have hv:=(hp.comp (fp_fst f BitEncoding.nat)).comp (fp_snd e e)
  have hb:=he.ite (fp_const _ e (constant n 1)) hv
  exact (((fp_fst BitEncoding.nat f.list).pair
    ((fp_snd BitEncoding.nat f.list).comp (ListIndexMachines.fp_zipIdx f))).comp
      (ListContextMachines.fp_mapWithContext BitEncoding.nat (f.prod BitEncoding.nat) e _ hb)).congr
        (fun p=>by simp only [otherDenominators,Function.comp_def,decide_eq_true_eq])

 theorem fp_commonDenominator (n:ℕ) : FP (fractionEncoding n).list (encoding n) (commonDenominator n) :=
  (ListMapMachines.fp_map (fractionEncoding n) (encoding n) Prod.snd (fp_snd (encoding n) (encoding n))).comp
    (fp_productGrid n)

 theorem fp_clearNumerator (n:ℕ) : FP (BitEncoding.nat.prod (fractionEncoding n).list)
    (encoding n) (fun p=>clearNumerator n p.2 p.1) := by
  have hn:=(fp_codeLookup (fractionEncoding n) (fractionZero n)).comp (fp_fst (encoding n) (encoding n))
  have hp:=(fp_otherDenominators n).comp (fp_productGrid n)
  exact (hn.pair hp).comp (fp_mul n)

end PlanarHom.DensePolynomial
