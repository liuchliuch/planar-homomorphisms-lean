import PlanarHom.DensePolynomialProductGrid
import PlanarHom.VariableDeterminantCorrectness

/-! NEW actual variable-order polynomial determinant over the concrete dense
code. Ragged/missing entries are zero; dimension of the coefficient ring alone
is fixed. All evaluations call the proved rational determinant machine. -/
noncomputable section
namespace PlanarHom.DensePolynomial
open Complexity PairProjectionMachines

 def matrixEntry (n:ℕ) (g:List (List (Code n))) (i j:ℕ) : Code n :=
    ((g[i]?.getD [])[j]?).getD (zero n)

 def matrixValue (n:ℕ) (g:List (List (Code n))) : Matrix (Fin g.length) (Fin g.length) (Poly n) :=
    fun i j=>interpret n (matrixEntry n g i.val j.val)

 theorem matrix_entry_degree (n:ℕ) (g:List (List (Code n))) (i j:ℕ) :
    BoxDegree n ((encoding n).list.list.encode g).length (interpret n (matrixEntry n g i j)) := by
  unfold matrixEntry
  cases he:g[i]? with
  | none=>simpa [he] using boxDegree_zero n ((encoding n).list.list.encode g).length
  | some row=>
    simp only [he,Option.getD_some]
    exact boxDegree_mono n (codeLength_member (encoding n).list (List.mem_of_getElem? he)) (boxDegree_lookup n row j)

 theorem determinant_input_degree (n:ℕ) (g:List (List (Code n))) :
    BoxDegree n (inputSquare (encoding n).list.list g) (matrixValue n g).det := by
  have h:=boxDegree_determinant n ((encoding n).list.list.encode g).length (matrixValue n g)
    (fun i j=>matrix_entry_degree n g i.val j.val)
  apply boxDegree_mono n _ h
  simp only [Fintype.card_fin,inputSquare,pow_two]
  exact Nat.mul_le_mul_right _ (BitEncoding.list_length_le (encoding n).list g)

 def matrixSample (n:ℕ) (g:List (List (Code n))) (point:List ℚ) : List (List ℚ) :=
    (List.range g.length).map (fun i=>(List.range g.length).map
      (fun j=>evaluate n (matrixEntry n g i j) point))

 def determinantSample (n:ℕ) (g:List (List (Code n))) (point:List ℚ) : ℚ :=
    VariableDeterminant.determinant (matrixSample n g point)

 def determinantGrid (n:ℕ) (g:List (List (Code n))) : Code n :=
    gridRecover n (inputSquare (encoding n).list.list g) (determinantSample n g)

 theorem determinantSample_eq (n:ℕ) (g:List (List (Code n))) (point:List ℚ) :
    determinantSample n g point=evalHom n point (matrixValue n g).det := by
  rw [determinantSample,matrixSample,VariableDeterminant.range_map_eq_ofFn]
  simp only [VariableDeterminant.range_map_eq_ofFn,evaluate_semantics]
  rw [VariableDeterminant.determinant_ofFn rationalBasis]
  exact (RingHom.map_det (evalHom n point) (matrixValue n g)).symm

 theorem determinantGrid_eq (n:ℕ) (g:List (List (Code n))) :
    interpret n (determinantGrid n g)=(matrixValue n g).det :=
  gridRecover_eq n _ _ _ (determinant_input_degree n g) (fun point _=>determinantSample_eq n g point)

 theorem fp_codeLookup {A:Type} (e:BitEncoding A) (z:A) :
    FP (BitEncoding.nat.prod e.list) e (fun p=>p.2[p.1]?.getD z) :=
  ((ListDropMachines.fp_drop e z).comp (ListDecompositionMachines.fp_headD e z)).congr
    (fun p=>by simp only [Function.comp_apply,List.headD_eq_head?_getD,List.head?_drop])

 theorem fp_matrixEntry (n:ℕ) : FP ((encoding n).list.list.prod (BitEncoding.nat.prod BitEncoding.nat))
    (encoding n) (fun p=>matrixEntry n p.1 p.2.1 p.2.2) := by
  let e:=encoding n
  have hg:=fp_fst e.list.list (BitEncoding.nat.prod BitEncoding.nat)
  have hi:=(fp_snd e.list.list (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj:=(fp_snd e.list.list (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  have hr:=(hi.pair hg).comp (fp_codeLookup e.list [])
  exact (hj.pair hr).comp (fp_codeLookup e (zero n))

 theorem fp_matrixSample (n:ℕ) : FP ((encoding n).list.list.prod rationalCode.list) rationalCode.list.list
    (fun p=>matrixSample n p.1 p.2) := by
  let e:=encoding n
  let ec:=e.list.list.prod rationalCode.list
  let ei:=ec.prod BitEncoding.nat
  have hg:=fp_fst e.list.list rationalCode.list
  have hp:=fp_snd e.list.list rationalCode.list
  have hr:=(hg.comp (ListUnaryLengthMachine.fp_length e.list)).comp UnaryArithmeticMachines.fp_range
  have hb:=fp_fst ei BitEncoding.nat
  have hc:=hb.comp (fp_fst ec BitEncoding.nat)
  have hi:=hb.comp (fp_snd ec BitEncoding.nat)
  have hj:=fp_snd ei BitEncoding.nat
  have he:=((hc.comp hg).pair (hi.pair hj)).comp (fp_matrixEntry n)
  have hv:=(he.pair (hc.comp hp)).comp (fp_evaluate n)
  have inner:=(((fp_id ei).pair ((fp_fst ec BitEncoding.nat).comp hr)).comp
    (ListContextMachines.fp_mapWithContext ei BitEncoding.nat rationalCode _ hv))
  exact (((fp_id ec).pair hr).comp
    (ListContextMachines.fp_mapWithContext ec BitEncoding.nat rationalCode.list _ inner))

 theorem fp_determinantSample (n:ℕ) : FP ((encoding n).list.list.prod rationalCode.list) rationalCode
    (fun p=>determinantSample n p.1 p.2) :=
  (fp_matrixSample n).comp (VariableDeterminant.fp_determinant rationalBasis)

 theorem fp_determinantGrid (n:ℕ) : FP (encoding n).list.list (encoding n) (determinantGrid n) :=
  ((fp_inputSquare (encoding n).list.list).pair (fp_id (encoding n).list.list)).comp
    (fp_gridRecover (encoding n).list.list (determinantSample n) (fp_determinantSample n) n)

end PlanarHom.DensePolynomial
