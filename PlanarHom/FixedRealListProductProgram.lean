import PlanarHom.FixedRealInterpolationRecovery
import PlanarHom.ConditionalMachines
import PlanarHom.NatListSumMachines

/-! Variable-length multiplication of arbitrary represented extension values.
A lower unit-bidiagonal system is materialized and solved by the actual
polynomial extension solver. No unreduced fraction-fold bound is assumed. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealListProduct
open DensePolynomial Complexity FixedRealExtension PairProjectionMachines
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def one : Code n e := (presentation basis).constant 1
def negative (a:Code n e) : Code n e :=
  FixedRealExtension.mul (multiplicationTable basis) ((presentation basis).constant (-1)) a

def entry (xs:List (Code n e)) (i j:ℕ) : Code n e :=
  if i=j then one basis else if i=j+1 then negative basis (xs[j]?.getD (zeroCode n e)) else zeroCode n e

def program (xs:List (Code n e)) : System n e :=
  ((List.range (xs.length+1)).map (fun i=>(List.range (xs.length+1)).map (entry basis xs i)),
    (List.range (xs.length+1)).map (fun i=>if i=0 then one basis else zeroCode n e))

def product (xs:List (Code n e)) : Code n e :=
  (solve (multiplicationTable basis) (program basis xs))[xs.length]?.getD (zeroCode n e)

theorem fp_negative : FP (encoding n e) (encoding n e) (negative basis) :=
  ((fp_const _ (encoding n e) ((presentation basis).constant (-1))).pair (fp_id _)).comp
    (FixedRealExtension.fp_mul n e (multiplicationTable basis))

def entryEncoding (n e:ℕ) := ((encoding n e).list.prod BitEncoding.nat).prod BitEncoding.nat

theorem fp_entry : FP (entryEncoding n e) (encoding n e) (fun p=>entry basis p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst ((encoding n e).list.prod BitEncoding.nat) BitEncoding.nat
  have hi:=hc.comp (fp_snd (encoding n e).list BitEncoding.nat)
  have hx:=hc.comp (fp_fst (encoding n e).list BitEncoding.nat)
  have hj:=fp_snd ((encoding n e).list.prod BitEncoding.nat) BitEncoding.nat
  have heq:=(hi.pair hj).comp NatListSumMachines.fp_equal
  have hsucc:=(hi.pair (hj.comp BinaryArithmetic.fp_successor)).comp NatListSumMachines.fp_equal
  have ha:=(hj.pair hx).comp (fp_codeLookup (encoding n e) (zeroCode n e))
  exact heq.ite (fp_const _ _ (one basis))
    (hsucc.ite (ha.comp (fp_negative basis)) (fp_const _ _ (zeroCode n e)))

theorem fp_rangeMap {D C:Type} (ed:BitEncoding D) (ec:BitEncoding C) (N:D→ℕ)
    (hN:FP ed BitEncoding.unaryNat N) (f:D→ℕ→C)
    (hf:FP (ed.prod BitEncoding.nat) ec (fun p=>f p.1 p.2)) :
    FP ed ec.list (fun d=>(List.range (N d)).map (f d)) := by
  have hr:=(UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
    (fun n=>List.reverse_reverse (List.range n))
  exact ((fp_id ed).pair (hN.comp hr)).comp (ListContextMachines.fp_mapWithContext ed BitEncoding.nat ec _ hf)

theorem fp_order : FP (encoding n e).list BitEncoding.unaryNat (fun xs=>xs.length+1) :=
  ((ListUnaryLengthMachine.fp_length (encoding n e)).comp (UnaryPolynomialMachines.fp_offset 1)).congr (fun xs=>Nat.add_comm 1 xs.length)

theorem fp_program : FP (encoding n e).list (systemEncoding n e) (program basis) := by
  let ec:=encoding n e
  have hr:FP (ec.list.prod BitEncoding.nat) ec.list
      (fun p=>(List.range (p.1.length+1)).map (entry basis p.1 p.2)):=
    fp_rangeMap (ec.list.prod BitEncoding.nat) ec (fun p=>p.1.length+1)
      ((fp_fst ec.list BitEncoding.nat).comp fp_order) _ (fp_entry basis)
  have hm:=fp_rangeMap ec.list ec.list (fun xs=>xs.length+1) fp_order
    (fun xs i=>(List.range (xs.length+1)).map (entry basis xs i)) hr
  have hi:=fp_snd ec.list BitEncoding.nat
  have hb:=((hi.pair (fp_const _ BitEncoding.nat 0)).comp NatListSumMachines.fp_equal).ite
    (fp_const _ ec (one basis)) (fp_const _ ec (zeroCode n e))
  exact hm.pair (fp_rangeMap ec.list ec (fun xs=>xs.length+1) fp_order (fun _ i=>if i=0 then one basis else zeroCode n e) hb)

theorem fp_product : FP (encoding n e).list (encoding n e) (product basis) :=
  ((ListCodecMachines.fp_length (encoding n e)).pair
    ((fp_program basis).comp (fp_solve (multiplicationTable basis)))).comp
      (fp_codeLookup (encoding n e) (zeroCode n e))

@[simp] theorem program_order (xs:List (Code n e)) : (program basis xs).1.length=xs.length+1 := by simp [program]

theorem one_valid : Valid n (one basis) := (presentation basis).constant_valid 1
@[simp] theorem one_value : value basis (one basis)=1 := (presentation basis).constant_value 1

theorem negative_valid (a:Code n e) (ha:Valid n a) : Valid n (negative basis a) :=
  mul_valid _ _ _ ((presentation basis).constant_valid _) ha

@[simp] theorem negative_value (a:Code n e) : value basis (negative basis a)= -value basis a := by
  rw [negative,value_mul _ basis (multiplicationTable_realizes basis)]
  have hc:value basis ((presentation basis).constant (-1))= -1:=(presentation basis).constant_value _
  rw [hc,neg_one_mul]

theorem entry_valid (xs:List (Code n e)) (h:∀x∈xs,Valid n x) (i j:ℕ) : Valid n (entry basis xs i j) := by
  unfold entry
  split
  · exact one_valid basis
  · split
    · exact negative_valid basis _ (codeLookup_valid xs j h)
    · exact zeroCode_valid n e

theorem program_valid (xs:List (Code n e)) (h:∀x∈xs,Valid n x) : SystemValid n e (program basis xs) := by
  constructor
  · intro row hr c hc
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hr
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hc
    exact entry_valid basis xs h i j
  · intro c hc
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hc
    split
    · exact one_valid basis
    · exact zeroCode_valid n e

end PlanarHom.FixedRealListProduct
