import PlanarHom.FixedExtensionMatrixEntries
import PlanarHom.DenseRationalSystemProgram
import Mathlib.Data.List.OfFn
import Mathlib.Logic.Equiv.Fin.Basic

/-! Actual variable-order fixed-extension system expansion. Block indices are
row-major `(i,k)` and `(j,l)`, with the extension coordinate second. Every nested
list and every zero/default cell is materialized by an actual list machine. -/
noncomputable section
namespace PlanarHom.FixedRealExtension
open DensePolynomial Complexity PairProjectionMachines
variable {n e:ℕ}

abbrev System (n e:ℕ) := List (List (Code n e))×List (Code n e)
def systemEncoding (n e:ℕ) := (encoding n e).list.list.prod (encoding n e).list

def systemEntry (n e:ℕ) (p:System n e) (i j:ℕ) : Code n e :=
  ((p.1[i]?.getD [])[j]?).getD (zeroCode n e)
def systemRhs (n e:ℕ) (p:System n e) (i:ℕ) : Code n e :=
  p.2[i]?.getD (zeroCode n e)

def blockList {B:Type} (e N:ℕ) (f:ℕ→Fin e→B) : List B :=
  (List.range N).flatMap (fun i=>List.ofFn (f i))

theorem blockList_ofFn {B:Type} (e N:ℕ) (f:ℕ→Fin e→B) :
    blockList e N f=List.ofFn (fun z:Fin (N*e)=>
      f (finProdFinEquiv.symm z).1.val (finProdFinEquiv.symm z).2) := by
  rw [List.ofFn_mul]
  simp only [blockList,List.flatMap_def,VariableDeterminant.range_map_eq_ofFn]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext i
  apply congrArg List.ofFn
  funext k
  have he:(⟨i.val*e+k.val,by have h:=Nat.mul_le_mul_right e i.isLt; nlinarith [k.isLt]⟩:Fin (N*e))=finProdFinEquiv (i,k) := by
    apply Fin.ext
    simp only [finProdFinEquiv,Equiv.coe_fn_mk]
    ring
  rw [he,Equiv.symm_apply_apply]

@[simp] theorem blockList_length {B:Type} (e N:ℕ) (f:ℕ→Fin e→B) :
    (blockList e N f).length=N*e := by rw [blockList_ofFn,List.length_ofFn]

theorem fp_blockList {B C:Type} (eb:BitEncoding B) (ec:BitEncoding C) (e:ℕ)
    (N:B→ℕ) (hN:FP eb BitEncoding.unaryNat N) (f:B→ℕ→Fin e→C)
    (hf:∀k,FP (eb.prod BitEncoding.nat) ec (fun p=>f p.1 p.2 k)) :
    FP eb ec.list (fun b=>blockList e (N b) (f b)) := by
  have hv:FP (eb.prod BitEncoding.nat) (ec.vector e) (fun p=>f p.1 p.2) :=
    FixedVectorMachines.fp_assemble _ _ _ _ hf
  have hl:FP (eb.prod BitEncoding.nat) ec.list (fun p=>List.ofFn (f p.1 p.2)) :=
    hv.transportOutput (fun _=>rfl)
  have hr:=hN.comp UnaryArithmeticMachines.fp_range
  exact (((fp_id eb).pair hr).comp (ListContextMachines.fp_mapWithContext eb BitEncoding.nat ec.list _ hl)).comp
    (ListFlattenMachines.fp_flatten ec)

def expandedRow (T:MultiplicationTable n e) (p:System n e) (i:ℕ) (k:Fin e) : List (FractionCode n) :=
  blockList e p.1.length (fun j l=>blockEntry T (systemEntry n e p i j) k l)

def expand (T:MultiplicationTable n e) (p:System n e) : DensePolynomial.System n :=
  (blockList e p.1.length (expandedRow T p),
   blockList e p.1.length (fun i k=>((systemRhs n e p i).1 k,(systemRhs n e p i).2)))

theorem fp_systemEntry (n e:ℕ) : FP ((systemEncoding n e).prod (BitEncoding.nat.prod BitEncoding.nat))
    (encoding n e) (fun p=>systemEntry n e p.1 p.2.1 p.2.2) := by
  let ec:=encoding n e
  let es:=systemEncoding n e
  have hg:=(fp_fst es (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst ec.list.list ec.list)
  have hi:=(fp_snd es (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_fst BitEncoding.nat BitEncoding.nat)
  have hj:=(fp_snd es (BitEncoding.nat.prod BitEncoding.nat)).comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact (hj.pair ((hi.pair hg).comp (fp_codeLookup ec.list []))).comp (fp_codeLookup ec (zeroCode n e))

theorem fp_systemRhs (n e:ℕ) : FP ((systemEncoding n e).prod BitEncoding.nat) (encoding n e)
    (fun p=>systemRhs n e p.1 p.2) := by
  let ec:=encoding n e
  exact ((fp_snd (systemEncoding n e) BitEncoding.nat).pair
    ((fp_fst (systemEncoding n e) BitEncoding.nat).comp (fp_snd ec.list.list ec.list))).comp
      (fp_codeLookup ec (zeroCode n e))

theorem fp_systemOrder (n e:ℕ) : FP (systemEncoding n e) BitEncoding.unaryNat (fun p=>p.1.length) :=
  (fp_fst (encoding n e).list.list (encoding n e).list).comp (ListUnaryLengthMachine.fp_length (encoding n e).list)

theorem fp_expandedRow (T:MultiplicationTable n e) (k:Fin e) :
    FP ((systemEncoding n e).prod BitEncoding.nat) (fractionEncoding n).list
      (fun p=>expandedRow T p.1 p.2 k) := by
  let es:=systemEncoding n e
  let ei:=es.prod BitEncoding.nat
  have hc:=fp_fst ei BitEncoding.nat
  have hp:=hc.comp (fp_fst es BitEncoding.nat)
  have hi:=hc.comp (fp_snd es BitEncoding.nat)
  have hj:=fp_snd ei BitEncoding.nat
  apply fp_blockList ei (fractionEncoding n) e (fun p=>p.1.1.length)
    ((fp_fst es BitEncoding.nat).comp (fp_systemOrder n e))
  intro l
  exact ((hp.pair (hi.pair hj)).comp (fp_systemEntry n e)).comp (fp_blockEntry T k l)

theorem fp_expand (T:MultiplicationTable n e) :
    FP (systemEncoding n e) (DensePolynomial.systemEncoding n) (expand T) := by
  let es:=systemEncoding n e
  let ec:=encoding n e
  let ep:=DensePolynomial.encoding n
  have hm:=fp_blockList es (fractionEncoding n).list e _ (fp_systemOrder n e) _ (fp_expandedRow T)
  have hr:FP es (fractionEncoding n).list (fun p=>blockList e p.1.length
      (fun i k=>((systemRhs n e p i).1 k,(systemRhs n e p i).2))) := by
    apply fp_blockList es (fractionEncoding n) e _ (fp_systemOrder n e)
    intro k
    have hh:=fp_systemRhs n e
    have hn:=(hh.comp (fp_fst (ep.vector e) ep)).comp (FixedVectorMachines.fp_coordinate ep e k)
    exact hn.pair (hh.comp (fp_snd (ep.vector e) ep))
  exact hm.pair hr

end PlanarHom.FixedRealExtension
