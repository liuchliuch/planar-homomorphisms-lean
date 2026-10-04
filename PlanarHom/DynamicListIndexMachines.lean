import PlanarHom.PlanarityLRConstraintMachines

/-! NEW reconstruction. Exact first-index lookup for an arbitrary honestly
encoded type with a concrete equality machine. Missing entries return length. -/
namespace PlanarHom.DynamicListIndexMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives Polynomial
variable {A : Type} [DecidableEq A] [BEq A] [LawfulBEq A]

 def step (s : A×ℕ) (a : A) : A×ℕ := (s.1,if a=s.1 then 0 else s.2+1)

 theorem fp_step (ea : BitEncoding A)
    (heq : FP (ea.prod ea) BitEncoding.bool (fun p=>decide (p.1=p.2))) :
    FP ((ea.prod BitEncoding.nat).prod ea) (ea.prod BitEncoding.nat) (fun p=>step p.1 p.2) := by
  have hs:=fp_fst (ea.prod BitEncoding.nat) ea
  have hk:=hs.comp (fp_fst ea BitEncoding.nat)
  have hn:=hs.comp (fp_snd ea BitEncoding.nat)
  have ha:=fp_snd (ea.prod BitEncoding.nat) ea
  have ht:=(ha.pair hk).comp heq
  have hsucc:=hn.comp BinaryArithmetic.fp_successor
  exact hk.pair (ht.ite (fp_const _ BitEncoding.nat 0) hsucc)

 theorem nat_succ_length (n : ℕ) :
    (BitEncoding.nat.encode (n+1)).length≤(BitEncoding.nat.encode n).length+2 := by
  have hh:=BinaryArithmetic.addBits_length_le false (Computability.encodeNat n) (Computability.encodeNat 1)
  rw [BinaryArithmetic.addBits_encodeNat] at hh
  have hone : (Computability.encodeNat 1).length=1 := by simp [BinaryArithmetic.encodeNat_length]
  simpa only [BitEncoding.nat,hone,Nat.add_assoc] using hh

 theorem step_length (ea : BitEncoding A) (s : A×ℕ) (a : A) :
    ((ea.prod BitEncoding.nat).encode (step s a)).length ≤ ((ea.prod BitEncoding.nat).encode s).length+2 := by
  have hh:=nat_succ_length s.2
  simp only [step,BitEncoding.prod_length]
  split_ifs
  · have hz : (BitEncoding.nat.encode 0).length=0 := by simp [BitEncoding.nat,BinaryArithmetic.encodeNat_length]
    rw [hz]
    omega
  · omega

 theorem fold_length (ea : BitEncoding A) (s : A×ℕ) (xs : List A) :
    ((ea.prod BitEncoding.nat).encode (xs.foldl step s)).length ≤
      ((ea.prod BitEncoding.nat).encode s).length+2*xs.length := by
  induction xs generalizing s with
  | nil => simp
  | cons a xs ih =>
    have hh:=ih (step s a)
    have hs:=step_length ea s a
    simp only [List.foldl_cons,List.length_cons]
    omega

 theorem fold_reverse (key : A) (xs : List A) : xs.reverse.foldl step (key,0)=(key,xs.idxOf key) := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,ih,step,List.idxOf_cons]
    by_cases h:a=key <;> simp [h,Bool.beq_eq_decide_eq]

 theorem fp_index (ea : BitEncoding A)
    (heq : FP (ea.prod ea) BitEncoding.bool (fun p=>decide (p.1=p.2))) :
    FP (ea.prod ea.list) BitEncoding.nat (fun p=>p.2.idxOf p.1) := by
  have hfold:=ListFoldMachines.fp_foldl ea (ea.prod BitEncoding.nat) step (fp_step ea heq) (C 3*X) (by
    intro s xs i hi
    have hb:=fold_length ea s (xs.take i)
    have hl:=BitEncoding.list_length_le ea xs
    have ht:(xs.take i).length≤xs.length:=by simp
    simp only [eval_mul,eval_C,eval_X,BitEncoding.prod_length]
    simp only [BitEncoding.prod_length] at hb
    omega)
  have hk:=fp_fst ea ea.list
  have hx:=(fp_snd ea ea.list).comp (ListReverseMachines.fp_reverse ea)
  have hs:=hk.pair (fp_const (ea.prod ea.list) BitEncoding.nat 0)
  exact (((hs.pair hx).comp hfold).comp (fp_snd ea BitEncoding.nat)).congr
    (fun p=>by simp only [Function.comp_apply,fold_reverse])

end PlanarHom.DynamicListIndexMachines
