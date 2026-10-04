import PlanarHom.RoutingMachinePrimitives

/-! Actual finite-control compilation of complete numeric routing layers,
including binary indexing, passive wires, and honestly unary fresh allocation. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives

abbrev SpliceInput := ℕ × (List ℕ × (Instruction × List ℕ))
def spliceEncoding : BitEncoding SpliceInput :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.list.prod (instructionEncoding.prod BitEncoding.nat.list))

def splice (fresh : ℕ) (outputs : List ℕ) (p : SpliceInput) : LayerResult :=
  let base := p.1+6*p.2.1.length
  ⟨base+fresh+6*p.2.2.2.length,
    wireRails p.1 p.2.1++outputs.map (fun i => base+i)++wireRails (base+fresh) p.2.2.2,
    wireProgram p.2.1++p.2.2.1::wireProgram p.2.2.2⟩

theorem fp_splice (fresh : ℕ) (outputs : List ℕ) : FP spliceEncoding layerEncoding (splice fresh outputs) := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.nat.list.prod (instructionEncoding.prod BitEncoding.nat.list))
  have hrest := fp_snd BitEncoding.unaryNat (BitEncoding.nat.list.prod (instructionEncoding.prod BitEncoding.nat.list))
  have hpre := hrest.comp (fp_fst BitEncoding.nat.list (instructionEncoding.prod BitEncoding.nat.list))
  have hlast := hrest.comp (fp_snd BitEncoding.nat.list (instructionEncoding.prod BitEncoding.nat.list))
  have hop := hlast.comp (fp_fst instructionEncoding BitEncoding.nat.list)
  have htail := hlast.comp (fp_snd instructionEncoding BitEncoding.nat.list)
  have hprelen := hpre.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)
  have htaillen := htail.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)
  have hsixpre := ((fp_const _ BitEncoding.unaryNat 6).pair hprelen).comp UnaryPolynomialMachines.fp_mul
  have hsixtail := ((fp_const _ BitEncoding.unaryNat 6).pair htaillen).comp UnaryPolynomialMachines.fp_mul
  have hbase := (hm.pair hsixpre).comp UnaryPolynomialMachines.fp_add
  have hbase' := (hbase.pair (fp_const _ BitEncoding.unaryNat fresh)).comp UnaryPolynomialMachines.fp_add
  have hcount := (hbase'.pair hsixtail).comp UnaryPolynomialMachines.fp_add
  have hprefix := (hm.pair hpre).comp fp_wireRails
  have hsuffix := (hbase'.pair htail).comp fp_wireRails
  have houtputs := (((hbase.comp UnaryNatConversionMachine.fp_conversion).pair
    (fp_const spliceEncoding BitEncoding.nat.list outputs)).comp
      (ListContextMachines.fp_mapWithContext BitEncoding.nat BitEncoding.nat BitEncoding.nat
        (fun p : ℕ × ℕ => p.1+p.2) BinaryArithmetic.fp_addition))
  have hfirst := (hprefix.pair houtputs).comp (ListMutationMachines.fp_append BitEncoding.nat)
  have hrails := (hfirst.pair hsuffix).comp (ListMutationMachines.fp_append BitEncoding.nat)
  have hcodepre := hpre.comp fp_wireProgram
  have hcodetail := htail.comp fp_wireProgram
  have hlastcode := (hop.pair hcodetail).comp (ListMutationMachines.fp_cons instructionEncoding)
  have hcode := (hcodepre.pair hlastcode).comp (ListMutationMachines.fp_append instructionEncoding)
  exact (hcount.pair (hrails.pair hcode)).comp fp_layerBuild

private theorem swapLayer_split (m : ℕ) (pre tail : List ℕ) (a b : ℕ) :
    swapLayer m pre.length (pre++a::b::tail)=splice 15 [0,1] (m,(pre,(crossing a b,tail))) := by
  induction pre generalizing m with
  | nil => simp [swapLayer,splice,passive,wireRails,wireProgram]
  | cons x pre ih =>
    simp only [List.length_cons,List.cons_append,swapLayer,ih]
    simp [splice,wireRails,wireProgram,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem copyLayer_split (m : ℕ) (pre tail : List ℕ) (a : ℕ) :
    copyLayer m pre.length (pre++a::tail)=splice 12 [1,0] (m,(pre,(fan a,tail))) := by
  induction pre generalizing m with
  | nil => simp [copyLayer,splice,passive,wireRails,wireProgram]
  | cons x pre ih =>
    simp only [List.length_cons,List.cons_append,copyLayer,ih]
    simp [splice,wireRails,wireProgram,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem swapLayer_invalid (i m : ℕ) (rs : List ℕ) (hi : rs.length≤ i+1) :
    swapLayer m i rs=passive m rs := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => rfl
    | cons a rs => cases rs with
      | nil => rfl
      | cons b rs => simp at hi
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      have h := ih (m+6) rs (by simp only [List.length_cons] at hi; omega)
      simp [swapLayer,h,passive,wireRails,wireProgram,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem copyLayer_invalid (i m : ℕ) (rs : List ℕ) (hi : rs.length≤ i) : copyLayer m i rs=passive m rs := by
  induction i generalizing m rs with
  | zero => have h : rs=[] := List.length_eq_zero.mp (by omega); subst rs; rfl
  | succ i ih =>
    cases rs with
    | nil => rfl
    | cons a rs =>
      have h := ih (m+6) rs (by simp only [List.length_cons] at hi; omega)
      simp [copyLayer,h,passive,wireRails,wireProgram,Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

private theorem split_ref (rs : List ℕ) (i : ℕ) (hi : i<rs.length) :
    rs=rs.take i++getRef rs i::rs.drop (i+1) := by
  simp only [getRef,List.getElem?_eq_getElem hi,Option.getD_some]
  rw [List.getElem_cons_drop hi,List.take_append_drop]

private theorem split_refs (rs : List ℕ) (i : ℕ) (hi : i+1<rs.length) :
    rs=rs.take i++getRef rs i::getRef rs (i+1)::rs.drop (i+2) := by
  have h0 : i<rs.length := by omega
  simp only [getRef,List.getElem?_eq_getElem h0,List.getElem?_eq_getElem hi,Option.getD_some]
  rw [show i+2=(i+1)+1 by omega,List.getElem_cons_drop hi,List.getElem_cons_drop h0,List.take_append_drop]

theorem swapLayer_splice (m i : ℕ) (rs : List ℕ) :
    swapLayer m i rs=if i+1<rs.length then
      splice 15 [0,1] (m,(rs.take i,(crossing (getRef rs i) (getRef rs (i+1)),rs.drop (i+2))))
    else passive m rs := by
  by_cases hi : i+1<rs.length
  · rw [if_pos hi]
    have h := swapLayer_split m (rs.take i) (rs.drop (i+2)) (getRef rs i) (getRef rs (i+1))
    rw [List.length_take_of_le (by omega),←split_refs rs i hi] at h
    exact h
  · rw [if_neg hi]
    exact swapLayer_invalid i m rs (by omega)

theorem copyLayer_splice (m i : ℕ) (rs : List ℕ) :
    copyLayer m i rs=if i<rs.length then
      splice 12 [1,0] (m,(rs.take i,(fan (getRef rs i),rs.drop (i+1))))
    else passive m rs := by
  by_cases hi : i<rs.length
  · rw [if_pos hi]
    have h := copyLayer_split m (rs.take i) (rs.drop (i+1)) (getRef rs i)
    rw [List.length_take_of_le hi.le,←split_ref rs i hi] at h
    exact h
  · rw [if_neg hi]
    exact copyLayer_invalid i m rs (by omega)

def layerInputEncoding : BitEncoding (ℕ × (ℕ × List ℕ)) :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat.list)

theorem fp_swapLayer : FP layerInputEncoding layerEncoding (fun p => swapLayer p.1 p.2.1 p.2.2) := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hr := fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hi := hr.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hs := hr.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hi1 := (hi.pair (fp_const _ BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hi2 := (hi.pair (fp_const _ BitEncoding.nat 2)).comp BinaryArithmetic.fp_addition
  have hp := (hi.pair hs).comp (fp_take BitEncoding.nat 0)
  have ht := (hi2.pair hs).comp (ListDropMachines.fp_drop BitEncoding.nat 0)
  have hx := (hs.pair hi).comp fp_getRef
  have hy := (hs.pair hi1).comp fp_getRef
  have ho := (hx.pair hy).comp fp_crossing
  have hyes := (hm.pair (hp.pair (ho.pair ht))).comp (fp_splice 15 [0,1])
  have hno := (hm.pair hs).comp fp_passive
  have hlen := (hs.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)).comp UnaryNatConversionMachine.fp_conversion
  have htest := (hi1.pair hlen).comp BinaryArithmetic.fp_comparison
  exact (htest.ite hyes hno).congr (fun p => (swapLayer_splice p.1 p.2.1 p.2.2).symm)

theorem fp_copyLayer : FP layerInputEncoding layerEncoding (fun p => copyLayer p.1 p.2.1 p.2.2) := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hr := fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hi := hr.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hs := hr.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hi1 := (hi.pair (fp_const _ BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hp := (hi.pair hs).comp (fp_take BitEncoding.nat 0)
  have ht := (hi1.pair hs).comp (ListDropMachines.fp_drop BitEncoding.nat 0)
  have ho := ((hs.pair hi).comp fp_getRef).comp fp_fan
  have hyes := (hm.pair (hp.pair (ho.pair ht))).comp (fp_splice 12 [1,0])
  have hno := (hm.pair hs).comp fp_passive
  have hlen := (hs.comp (ListUnaryLengthMachine.fp_length BitEncoding.nat)).comp UnaryNatConversionMachine.fp_conversion
  have htest := (hi.pair hlen).comp BinaryArithmetic.fp_comparison
  exact (htest.ite hyes hno).congr (fun p => (copyLayer_splice p.1 p.2.1 p.2.2).symm)

theorem fp_checkLayer : FP layerInputEncoding layerEncoding (fun p => checkLayer p.2.1 p.1 p.2.2) := by
  have hm := fp_fst BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hr := fp_snd BitEncoding.unaryNat (BitEncoding.nat.prod BitEncoding.nat.list)
  have hi := hr.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hs := hr.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  have hi1 := (hi.pair (fp_const _ BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hi2 := (hi.pair (fp_const _ BitEncoding.nat 2)).comp BinaryArithmetic.fp_addition
  have hp := (hi.pair hs).comp (fp_take BitEncoding.nat 0)
  have hpassive := (hm.pair hp).comp fp_passive
  have hx := (hs.pair hi).comp fp_getRef
  have hy := (hs.pair hi1).comp fp_getRef
  have hz := (hs.pair hi2).comp fp_getRef
  have htest := (hx.pair (hy.pair hz)).comp fp_test
  have hcode := ((hpassive.comp fp_layerInstructions).pair
    (fp_singleton _ instructionEncoding _ htest)).comp (ListMutationMachines.fp_append instructionEncoding)
  exact ((hpassive.comp fp_layerCount).pair ((hpassive.comp fp_layerRails).pair hcode)).comp fp_layerBuild

end PlanarHom.PositiveBlockProgram
