import PlanarHom.FixedExtensionMatrixEntries
import PlanarHom.FixedRealAlphabetPresentation

/-! Actual polynomial-time addition of an arbitrary materialized list of fixed
extension representatives. All denominators are cleared in one grid product,
then numerators are summed; no repeated unreduced fraction-addition occurs. -/
noncomputable section
open scoped BigOperators
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines
variable {n e:ℕ}

def coordinateFractions (n:ℕ) (xs:List (Code n e)) (k:Fin e) : List (FractionCode n) :=
  xs.map (fun a=>(a.1 k,a.2))
def sumDenominator (n:ℕ) (xs:List (Code n e)) : DensePolynomial.Code n := productGrid n (xs.map Prod.snd)
def sumCoordinate (n:ℕ) (xs:List (Code n e)) (k:Fin e) : DensePolynomial.Code n :=
  DensePolynomial.sum n ((List.range xs.length).map (fun i=>clearNumerator n (coordinateFractions n xs k) i))
def sumList (n e:ℕ) (xs:List (Code n e)) : Code n e :=
  (fun k=>sumCoordinate n xs k,sumDenominator n xs)

theorem coordinateFractions_denominator (xs:List (Code n e)) (k:Fin e) :
    commonDenominator n (coordinateFractions n xs k)=sumDenominator n xs := by
  simp only [commonDenominator,coordinateFractions,List.map_map,Function.comp_def,sumDenominator]

theorem sumList_valid (xs:List (Code n e)) (h:∀a∈xs,Valid n a) : Valid n (sumList n e xs) := by
  change interpret n (productGrid n (xs.map Prod.snd))≠0
  rw [productGrid_eq]
  apply List.prod_ne_zero
  intro hm
  obtain ⟨p,hp,hz⟩:=List.mem_map.mp hm
  obtain ⟨a,ha,rfl⟩:=List.mem_map.mp hp
  exact h a ha hz

theorem clearNumerator_list_value (xs:List (FractionCode n)) (i:Fin xs.length)
    (hi:FractionValid n (xs.get i)) :
    algebraMap (Poly n) (RationalFunction n) (interpret n (clearNumerator n xs i.val))=
      algebraMap (Poly n) (RationalFunction n) (interpret n (commonDenominator n xs))*fractionValue n (xs.get i) := by
  simpa only [List.ofFn_get] using clearNumerator_value n (fun j:Fin xs.length=>xs.get j) i hi

theorem sumCoordinate_value (xs:List (Code n e)) (h:∀a∈xs,Valid n a) (k:Fin e) :
    algebraMap (Poly n) (RationalFunction n) (interpret n (sumCoordinate n xs k))=
      algebraMap (Poly n) (RationalFunction n) (interpret n (sumDenominator n xs))*
        (xs.map (fun a=>coordinates n a k)).sum := by
  let fs:=coordinateFractions n xs k
  have hlen:fs.length=xs.length:=by simp [fs,coordinateFractions]
  have hf:∀i:Fin xs.length,FractionValid n (fs.get ⟨i.val,by omega⟩) := by
    intro i
    change interpret n ((xs.map (fun a=>(a.1 k,a.2))).get ⟨i.val,by simpa [fs,coordinateFractions] using i.isLt⟩).2≠0
    simpa only [List.get_eq_getElem,List.getElem_map] using h (xs.get i) (List.get_mem xs i)
  have hc:∀i:Fin xs.length,
      algebraMap (Poly n) (RationalFunction n) (interpret n (clearNumerator n fs i.val))=
        algebraMap (Poly n) (RationalFunction n) (interpret n (sumDenominator n xs))*coordinates n (xs.get i) k := by
    intro i
    have hh:=clearNumerator_list_value fs ⟨i.val,by omega⟩ (hf i)
    rw [coordinateFractions_denominator] at hh
    simpa only [fs,coordinateFractions,List.get_eq_getElem,List.getElem_map,coordinates] using hh
  calc
    _ = ∑i:Fin xs.length,algebraMap (Poly n) (RationalFunction n)
        (interpret n (clearNumerator n fs i.val)) := by
      rw [sumCoordinate,VariableDeterminant.range_map_eq_ofFn,interpret_sum,
        List.map_ofFn,List.sum_ofFn,map_sum]
      rfl
    _ = ∑i:Fin xs.length,algebraMap (Poly n) (RationalFunction n)
        (interpret n (sumDenominator n xs))*coordinates n (xs.get i) k :=
      Finset.sum_congr rfl (fun i _=>hc i)
    _ = _ := by
      rw [←Finset.mul_sum,←List.sum_ofFn]
      congr 1
      have he:=List.map_ofFn (fun i:Fin xs.length=>xs.get i) (fun a=>coordinates n a k)
      rw [List.ofFn_get] at he
      exact congrArg List.sum he.symm

theorem coordinates_sumList (xs:List (Code n e)) (h:∀a∈xs,Valid n a) (k:Fin e) :
    coordinates n (sumList n e xs) k=(xs.map (fun a=>coordinates n a k)).sum := by
  change algebraMap (Poly n) (RationalFunction n) (interpret n (sumCoordinate n xs k)) /
    algebraMap (Poly n) (RationalFunction n) (interpret n (sumDenominator n xs))=_
  rw [sumCoordinate_value xs h k]
  apply mul_div_cancel_left₀
  exact fun hz=>sumList_valid xs h ((IsFractionRing.to_map_eq_zero_iff).mp hz)

theorem value_sumList {K:Type} [Field K] [Algebra (RationalFunction n) K]
    (basis:Module.Basis (Fin e) (RationalFunction n) K) (xs:List (Code n e))
    (h:∀a∈xs,Valid n a) : value basis (sumList n e xs)=(xs.map (value basis)).sum := by
  apply basis.equivFun.injective
  simp only [value,LinearEquiv.apply_symm_apply,map_list_sum,List.map_map,Function.comp_def]
  funext k
  rw [coordinates_sumList xs h k]
  have hh : ∀ys:List (Fin e→RationalFunction n),ys.sum k=(ys.map (fun f=>f k)).sum := by
    intro ys
    induction ys with
    | nil=>rfl
    | cons y ys ih=>simpa using ih
  rw [hh]
  simp only [List.map_map,Function.comp_def]

theorem fp_coordinateFractions (n e:ℕ) (k:Fin e) :
    FP (encoding n e).list (fractionEncoding n).list (fun xs=>coordinateFractions n xs k) := by
  let ep:=DensePolynomial.encoding n
  have hn:=(fp_fst (ep.vector e) ep).comp (FixedVectorMachines.fp_coordinate ep e k)
  exact ListMapMachines.fp_map (encoding n e) (fractionEncoding n) _ (hn.pair (fp_snd (ep.vector e) ep))

theorem fp_sumList (n e:ℕ) : FP (encoding n e).list (encoding n e) (sumList n e) := by
  let ec:=encoding n e
  let ep:=DensePolynomial.encoding n
  have hn:FP ec.list (ep.vector e) (fun xs k=>sumCoordinate n xs k) := by
    apply FixedVectorMachines.fp_assemble
    intro k
    have hf:=fp_coordinateFractions n e k
    have hr:=(ListUnaryLengthMachine.fp_length ec).comp UnaryArithmeticMachines.fp_range
    have hb:=((fp_snd (fractionEncoding n).list BitEncoding.nat).pair
      (fp_fst (fractionEncoding n).list BitEncoding.nat)).comp (fp_clearNumerator n)
    exact ((hf.pair hr).comp (ListContextMachines.fp_mapWithContext (fractionEncoding n).list BitEncoding.nat ep _ hb)).comp
      (DensePolynomial.fp_sum n)
  have hd:=(ListMapMachines.fp_map ec ep Prod.snd (fp_snd (ep.vector e) ep)).comp (fp_productGrid n)
  exact hn.pair hd

end PlanarHom.FixedRealExtension
