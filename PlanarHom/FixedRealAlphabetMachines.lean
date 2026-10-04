import PlanarHom.FixedRealAlphabetBounds
import PlanarHom.FixedRealExtensionMachines
import PlanarHom.RestrictedListFoldMachines
import PlanarHom.ListDropMachines

/-! Literal fixed-alphabet product machine, including every intermediate dense
coordinate in its polynomial runtime bound. The finite-symbol codec is the
ordinary binary natural-number word. -/
noncomputable section
namespace PlanarHom.FixedRealAlphabet
open DensePolynomial Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable {basis:Module.Basis (Fin e) (RationalFunction n) K} {A:Fin t→K}

def symbolEncoding (t:ℕ) : BitEncoding (Fin t) where
  encode a:=BitEncoding.nat.encode a.val
  decode raw:=do
    let a←BitEncoding.nat.decode raw
    if h:a<t then some ⟨a,h⟩ else none
  decode_encode a:=by simp [BitEncoding.nat.decode_encode,a.isLt]

theorem fp_symbol : FP (symbolEncoding t) BitEncoding.nat Fin.val :=
  fp_code_view _ _ _ (fun _=>rfl)

theorem fp_transition (d:Data basis A) (i j:Fin e) :
    FP (symbolEncoding t) (encoding n) (fun a=>d.transition a i j) := by
  let table:=List.ofFn (fun a=>d.transition a i j)
  have hd:=(fp_symbol.pair (fp_const (symbolEncoding t) (encoding n).list table)).comp
    (ListDropMachines.fp_drop (encoding n) (zero n))
  apply (hd.comp (ListDecompositionMachines.fp_headD (encoding n) (zero n))).congr
  intro a
  simp only [Function.comp_apply,table,List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,a.isLt,dif_pos,Option.getD_some]

theorem fp_step (d:Data basis A) :
    FP ((FixedRealExtension.encoding n e).prod (symbolEncoding t)) (FixedRealExtension.encoding n e)
      (fun p=>step d p.1 p.2) := by
  let ec:=FixedRealExtension.encoding n e
  let ep:=encoding n
  let ea:=symbolEncoding t
  have hs:=fp_fst ec ea
  have ha:=fp_snd ec ea
  have hn:FP (ec.prod ea) (ep.vector e) (fun p i=>
      fixedSum n e (fun j=>mul n (d.transition p.2 i j) (p.1.1 j))) := by
    apply FixedVectorMachines.fp_assemble
    intro i
    apply fp_fixedSum
    intro j
    have hnum:FP (ec.prod ea) ep (fun p=>p.1.1 j):=
      (hs.comp (fp_fst (ep.vector e) ep)).comp (FixedVectorMachines.fp_coordinate ep e j)
    exact ((ha.comp (fp_transition d i j)).pair hnum).comp (DensePolynomial.fp_mul n)
  have hden:FP (ec.prod ea) ep (fun p=>p.1.2):=hs.comp (fp_snd (ep.vector e) ep)
  exact hn.pair (((fp_const (ec.prod ea) ep d.denominator).pair hden).comp (DensePolynomial.fp_mul n))

def preparedEncoding (d:Data basis A) : BitEncoding (List (Fin t)) :=
  ((FixedRealExtension.encoding n e).prod (symbolEncoding t).list).retract
    (fun xs=>(initial d,xs)) Prod.snd (fun _=>rfl)

theorem fp_prepare (d:Data basis A) : FP (symbolEncoding t).list (preparedEncoding d) id :=
  ((fp_const (symbolEncoding t).list (FixedRealExtension.encoding n e) (initial d)).pair
    (fp_id (symbolEncoding t).list)).transportOutput (fun _=>rfl)

theorem fp_word (d:Data basis A) :
    FP (symbolEncoding t).list (FixedRealExtension.encoding n e) (word d) := by
  obtain ⟨body⟩:=fp_step d
  have hf:FP (preparedEncoding d) (FixedRealExtension.encoding n e) (word d) := by
    refine ⟨ListFoldMachines.computerOn (preparedEncoding d) (symbolEncoding t)
      (FixedRealExtension.encoding n e) (step d) (fun _=>initial d) id (fun _=>rfl)
      body (sizePolynomial (bounds d)) ?_⟩
    intro xs i hi
    have hb:=word_size d (xs.take i)
    have hlen: (xs.take i).length≤((preparedEncoding d).encode xs).length := by
      have hp:=BitEncoding.list_length_le (symbolEncoding t) xs
      simp only [preparedEncoding,BitEncoding.retract,BitEncoding.prod_length]
      have ht:(xs.take i).length≤xs.length:=by simp only [List.length_take]; exact Nat.min_le_right _ _
      omega
    exact hb.trans (MachineComposition.natPolynomial_monotone _ hlen)
  exact ((fp_prepare d).comp hf).congr (fun _=>rfl)

end PlanarHom.FixedRealAlphabet
