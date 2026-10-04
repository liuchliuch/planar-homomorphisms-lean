import PlanarHom.DensePolynomialCramer

/-! NEW total raw rational-function system program. Each literal row is cleared
with its own nonzero common denominator; square normalization uses zero/one for
missing cells. The result is computed by the actual polynomial Cramer machine. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 abbrev System (n:ℕ) := List (List (FractionCode n))×List (FractionCode n)
 def systemEncoding (n:ℕ) := (fractionEncoding n).list.list.prod (fractionEncoding n).list
 def systemEntry (n:ℕ) (p:System n) (i j:ℕ) := ((p.1[i]?.getD [])[j]?).getD (fractionZero n)
 def systemRhs (n:ℕ) (p:System n) (i:ℕ) := p.2[i]?.getD (fractionZero n)
 def rowFractions (n:ℕ) (p:System n) (i:ℕ) : List (FractionCode n) :=
    (List.range (p.1.length+1)).map (fun j=>if j=p.1.length then systemRhs n p i else systemEntry n p i j)
 def clearedSystem (n:ℕ) (p:System n) : List (List (Code n))×List (Code n) :=
    ((List.range p.1.length).map (fun i=>(List.range p.1.length).map
        (fun j=>clearNumerator n (rowFractions n p i) j)),
      (List.range p.1.length).map (fun i=>clearNumerator n (rowFractions n p i) p.1.length))
 def solve (n:ℕ) (p:System n) : List (FractionCode n) := solvePolynomial n (clearedSystem n p)

 theorem fp_systemEntry (n:ℕ) : FP ((systemEncoding n).prod (BitEncoding.nat.prod BitEncoding.nat))
    (fractionEncoding n) (fun p=>systemEntry n p.1 p.2.1 p.2.2) := by
  let e:=fractionEncoding n
  let ec:=systemEncoding n
  have hg:=(fp_fst ec (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst e.list.list e.list)
  have hi:=(fp_snd ec (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj:=(fp_snd ec (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact (hj.pair ((hi.pair hg).comp (fp_codeLookup e.list []))).comp (fp_codeLookup e (fractionZero n))

 theorem fp_systemRhs (n:ℕ) : FP ((systemEncoding n).prod BitEncoding.nat)
    (fractionEncoding n) (fun p=>systemRhs n p.1 p.2) := by
  let e:=fractionEncoding n
  exact ((fp_snd (systemEncoding n) BitEncoding.nat).pair
    ((fp_fst (systemEncoding n) BitEncoding.nat).comp (fp_snd e.list.list e.list))).comp
      (fp_codeLookup e (fractionZero n))

 theorem fp_systemOrder (n:ℕ) : FP (systemEncoding n) BitEncoding.unaryNat (fun p=>p.1.length) :=
  (fp_fst (fractionEncoding n).list.list (fractionEncoding n).list).comp
    (ListUnaryLengthMachine.fp_length (fractionEncoding n).list)

 theorem fp_rowFractions (n:ℕ) : FP ((systemEncoding n).prod BitEncoding.nat)
    (fractionEncoding n).list (fun p=>rowFractions n p.1 p.2) := by
  let ec:=systemEncoding n
  let ei:=ec.prod BitEncoding.nat
  have hp:=fp_fst ei BitEncoding.nat
  have hc:=hp.comp (fp_fst ec BitEncoding.nat)
  have hi:=hp.comp (fp_snd ec BitEncoding.nat)
  have hj:=fp_snd ei BitEncoding.nat
  have hn:=(hc.comp (fp_systemOrder n)).comp UnaryNatConversionMachine.fp_conversion
  have he:=(hj.pair hn).comp NatListSumMachines.fp_equal
  have ht:=(hc.pair hi).comp (fp_systemRhs n)
  have hf:=(hc.pair (hi.pair hj)).comp (fp_systemEntry n)
  have hr:=(((fp_fst ec BitEncoding.nat).comp (fp_systemOrder n)).comp
    UnaryArithmeticMachines.fp_succ).comp UnaryArithmeticMachines.fp_range
  exact (((fp_id ei).pair hr).comp
    (ListContextMachines.fp_mapWithContext ei BitEncoding.nat (fractionEncoding n) _ (he.ite ht hf))).congr
      (fun _=>by simp only [rowFractions,Function.comp_def,id_eq])

 theorem fp_clearedSystem (n:ℕ) : FP (systemEncoding n)
    ((encoding n).list.list.prod (encoding n).list) (clearedSystem n) := by
  let ec:=systemEncoding n
  let ei:=ec.prod BitEncoding.nat
  have hr:=(fp_systemOrder n).comp UnaryArithmeticMachines.fp_range
  have hb:=((fp_snd ei BitEncoding.nat).pair
    ((fp_fst ei BitEncoding.nat).comp (fp_rowFractions n))).comp (fp_clearNumerator n)
  have hi:=(((fp_id ei).pair ((fp_fst ec BitEncoding.nat).comp hr)).comp
    (ListContextMachines.fp_mapWithContext ei BitEncoding.nat (encoding n) _ hb))
  have hm:=((fp_id ec).pair hr).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat (encoding n).list _ hi)
  have hn:=((fp_fst ec BitEncoding.nat).comp (fp_systemOrder n)).comp UnaryNatConversionMachine.fp_conversion
  have ht:=(hn.pair (fp_rowFractions n)).comp (fp_clearNumerator n)
  have hv:=((fp_id ec).pair hr).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat (encoding n) _ ht)
  exact hm.pair hv

 theorem fp_solve (n:ℕ) : FP (systemEncoding n) (fractionEncoding n).list (solve n) :=
    (fp_clearedSystem n).comp (fp_solvePolynomial n)

end PlanarHom.DensePolynomial
