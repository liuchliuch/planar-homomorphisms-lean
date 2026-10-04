import PlanarHom.DensePolynomialCode

/-! Actual TM2 programs for every fixed number of polynomial variables.
No operation here treats rational or field arithmetic as unit cost. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

private theorem fp_lookup {A : Type} (e : BitEncoding A) (z:A) :
    FP (BitEncoding.nat.prod e.list) e (fun p=>p.2[p.1]?.getD z) := by
  exact ((ListDropMachines.fp_drop e z).comp (ListDecompositionMachines.fp_headD e z)).congr
    (fun p=>by simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop])

private theorem fp_gather {A : Type} (e : BitEncoding A) (z:A) :
    FP (BitEncoding.nat.prod e.list.list) e.list (fun p=>gather z p.1 p.2) :=
  ListContextMachines.fp_mapWithContext BitEncoding.nat e.list e
    (fun p=>p.2[p.1]?.getD z) (fp_lookup e z)

theorem fp_sum (n:ℕ) : FP (encoding n).list (encoding n) (sum n) := by
  induction n with
  | zero => exact MaterializedFieldListMachines.fp_sum rationalBasis
  | succ n ih =>
    let e:=encoding n
    let ei:=e.list.list
    have hg:=((fp_snd ei BitEncoding.nat).pair (fp_fst ei BitEncoding.nat)).comp (fp_gather e (zero n))
    have ht:=hg.comp ih
    have hr:=(fp_width e).comp UnaryArithmeticMachines.fp_range
    exact ((fp_id ei).pair hr).comp
      (ListContextMachines.fp_mapWithContext ei BitEncoding.nat e _ ht)

theorem fp_mul (n:ℕ) : FP ((encoding n).prod (encoding n)) (encoding n) (fun p=>mul n p.1 p.2) := by
  induction n with
  | zero => exact FixedFieldArithmetic.fp_multiplication rationalBasis
  | succ n ih =>
    let e:=encoding n
    let ec:=BitEncoding.unaryNat
    let ei:=e.list.prod e.list
    have hm:=(fp_snd ec (e.prod e)).comp ih
    have hs:=(fp_snd ec e.list).comp (fp_sum n)
    exact ((fp_const ei ec 0).pair (fp_id ei)).comp
      (CoefficientConvolutionMachines.fp_convolution e ec (zero n)
        (fun _ : ℕ=>mul n) (fun _ : ℕ=>sum n) hm hs)

theorem fp_neg (n:ℕ) : FP (encoding n) (encoding n) (neg n) := by
  induction n with
  | zero => exact FixedFieldArithmetic.fp_negation rationalBasis
  | succ n ih => exact ListMapMachines.fp_map (encoding n) (encoding n) _ ih

theorem fp_add (n:ℕ) : FP ((encoding n).prod (encoding n)) (encoding n) (fun p=>add n p.1 p.2) := by
  let e:=encoding n
  have ht:=((fp_snd e e).pair (fp_const (e.prod e) e.list [])).comp (ListMutationMachines.fp_cons e)
  have hl:=((fp_fst e e).pair ht).comp (ListMutationMachines.fp_cons e)
  exact hl.comp (fp_sum n)

theorem fp_isZero (n:ℕ) : FP (encoding n) BitEncoding.bool (isZero n) := by
  induction n with
  | zero =>
    exact ((fp_id (encoding 0)).pair (fp_const (encoding 0) (encoding 0) 0)).comp
      (FixedFieldArithmetic.fp_equality rationalBasis)
  | succ n ih =>
    have hn:=fp_bool_unary BitEncoding.bool Bool.not
    exact (ListPredicateMachines.fp_any (encoding n) _ (ih.comp hn)).comp hn

theorem fp_fractionMul (n:ℕ) :
    FP ((fractionEncoding n).prod (fractionEncoding n)) (fractionEncoding n)
      (fun p=>fractionMul n p.1 p.2) := by
  let e:=encoding n
  let f:=fractionEncoding n
  have ha:=fp_fst f f
  have hb:=fp_snd f f
  have han:=ha.comp (fp_fst e e)
  have had:=ha.comp (fp_snd e e)
  have hbn:=hb.comp (fp_fst e e)
  have hbd:=hb.comp (fp_snd e e)
  exact ((han.pair hbn).comp (fp_mul n)).pair ((had.pair hbd).comp (fp_mul n))

theorem fp_fractionAdd (n:ℕ) :
    FP ((fractionEncoding n).prod (fractionEncoding n)) (fractionEncoding n)
      (fun p=>fractionAdd n p.1 p.2) := by
  let e:=encoding n
  let f:=fractionEncoding n
  have ha:=fp_fst f f
  have hb:=fp_snd f f
  have han:=ha.comp (fp_fst e e)
  have had:=ha.comp (fp_snd e e)
  have hbn:=hb.comp (fp_fst e e)
  have hbd:=hb.comp (fp_snd e e)
  have hn:=(((han.pair hbd).comp (fp_mul n)).pair ((hbn.pair had).comp (fp_mul n))).comp (fp_add n)
  exact hn.pair ((had.pair hbd).comp (fp_mul n))

theorem fp_fractionNeg (n:ℕ) : FP (fractionEncoding n) (fractionEncoding n) (fractionNeg n) :=
  (((fp_fst (encoding n) (encoding n)).comp (fp_neg n)).pair (fp_snd (encoding n) (encoding n)))

theorem fp_fractionInv (n:ℕ) : FP (fractionEncoding n) (fractionEncoding n) (fractionInv n) :=
  (fp_snd (encoding n) (encoding n)).pair (fp_fst (encoding n) (encoding n))

theorem fp_fractionEq (n:ℕ) :
    FP ((fractionEncoding n).prod (fractionEncoding n)) BitEncoding.bool
      (fun p=>fractionEq n p.1 p.2) := by
  let e:=encoding n
  let f:=fractionEncoding n
  have ha:=fp_fst f f
  have hb:=fp_snd f f
  have han:=ha.comp (fp_fst e e)
  have had:=ha.comp (fp_snd e e)
  have hbn:=hb.comp (fp_fst e e)
  have hbd:=hb.comp (fp_snd e e)
  have hl:=(han.pair hbd).comp (fp_mul n)
  have hr:=((hbn.pair had).comp (fp_mul n)).comp (fp_neg n)
  exact ((hl.pair hr).comp (fp_add n)).comp (fp_isZero n)

end PlanarHom.DensePolynomial
