import PlanarHom.SignedIntegerAdditionBits
import PlanarHom.BinaryAdditionMachine

/-! # Linear-time signed integer addition on a fixed finite-control TM2 -/
namespace PlanarHom.BinaryArithmetic
open Turing Turing.TM2

structure SAddState where
  left : Bool
  right : Bool
  carry : Bool
  first : Option Bool
  second : Option Bool
  deriving Fintype

def saddInitial : SAddState := ⟨false,false,false,none,none⟩
def saddFlags (sa sb : Bool) : SAddState := ⟨sa,sb,false,none,none⟩
inductive SAddLabel | header | parse | rightHeader | reverse | add | trim | restore deriving DecidableEq,Fintype
abbrev SAddStmt := Stmt (fun _ : Option Bool => Bool) SAddLabel SAddState

def saddFinish : SAddStmt := .push none (fun _ => false) <| .push none (fun v => v.left) <|
  .push none (fun _ => true) (.load (fun _ => saddInitial) .halt)

def signedAdditionMachine : FinTM2 where
  K := Option Bool
  k₀ := none
  k₁ := none
  Γ _ := Bool
  Λ := SAddLabel
  main := .header
  σ := SAddState
  initialState := saddInitial
  m
    | .header => .pop none (fun v _ => v) <| .pop none (fun v _ => v) <|
        .pop none (fun v _ => v) <| .pop none (fun v b => {v with left := b.getD false}) <|
        .pop none (fun v _ => v) <| .pop none (fun v _ => v) (.goto (fun _ => .parse))
    | .parse => .pop none (fun v b => {v with first := b}) <|
        .branch (fun v => v.first.getD false)
          (.pop none (fun v b => {v with first := b}) <|
            .push (some false) (fun v => v.first.getD false) (.goto (fun _ => .parse)))
          (.goto (fun _ => .rightHeader))
    | .rightHeader => .pop none (fun v _ => v) <|
        .pop none (fun v b => {v with right := b.getD false}) <|
        .pop none (fun v _ => v) <|
        .load (fun v => saddFlags v.left v.right) (.goto (fun _ => .reverse))
    | .reverse => .pop (some false) (fun v b => {v with first := b}) <|
        .branch (fun v => v.first.isSome)
          (.push (some true) (fun v => v.first.getD false) (.goto (fun _ => .reverse)))
          (.load (fun v => saddFlags v.left v.right) (.goto (fun _ => .add)))
    | .add => .pop (some true) (fun v b => {v with first := b}) <|
        .pop none (fun v b => {v with second := b}) <|
          .branch (fun v => v.first.isSome || v.second.isSome)
            (.push (some false) (fun v => fullAdderBit (xor (v.first.getD false) v.left)
                (xor (v.second.getD false) v.right) v.carry) <|
              .load (fun v => {v with carry := (fullAdderCarry (xor (v.first.getD false) v.left)
                (xor (v.second.getD false) v.right) v.carry), first := none, second := none})
                (.goto (fun _ => .add)))
            (.push (some false) (fun v => fullAdderBit v.left v.right v.carry) <|
              .load (fun v => {saddInitial with left := (fullAdderBit v.left v.right
                (fullAdderCarry v.left v.right v.carry))}) (.goto (fun _ => .trim)))
    | .trim => .pop (some false) (fun v b => {v with first := b}) <|
        .branch (fun v => v.first.isSome)
          (.branch (fun v => xor (v.first.getD false) v.left)
            (.push none (fun _ => true) (.goto (fun _ => .restore))) (.goto (fun _ => .trim))) saddFinish
    | .restore => .pop (some false) (fun v b => {v with first := b}) <|
        .branch (fun v => v.first.isSome)
          (.push none (fun v => xor (v.first.getD false) v.left) (.goto (fun _ => .restore))) saddFinish

def saddCfg (l : Option SAddLabel) (v : SAddState) (ys bs xs : List Bool) : signedAdditionMachine.Cfg :=
  ⟨l,v,fun k : Option Bool => match k with | none => ys | some false => bs | some true => xs⟩

@[simp] theorem sadd_step_header (v : SAddState) (sa : Bool) (ys bs xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .header) v ([true,true,true,sa,true,false]++ys) bs xs) =
      some (saddCfg (some .parse) {v with left := sa} ys bs xs) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_parse_bit (v : SAddState) (b : Bool) (ys bs xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .parse) v (true::b::ys) bs xs) =
      some (saddCfg (some .parse) {v with first := some b} ys (b::bs) xs) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_parse_end (v : SAddState) (ys bs xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .parse) v (false::ys) bs xs) =
      some (saddCfg (some .rightHeader) {v with first := some false} ys bs xs) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_rightHeader (v : SAddState) (sb : Bool) (ys bs xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .rightHeader) v (true::sb::false::ys) bs xs) =
      some (saddCfg (some .reverse) (saddFlags v.left sb) ys bs xs) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_reverse_cons (v : SAddState) (b : Bool) (ys bs xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .reverse) v ys (b::bs) xs) =
      some (saddCfg (some .reverse) {v with first := some b} ys bs (b::xs)) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_reverse_nil (v : SAddState) (ys xs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .reverse) v ys [] xs) =
      some (saddCfg (some .add) (saddFlags v.left v.right) ys [] xs) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]

@[simp] theorem sadd_step_restore_cons (v : SAddState) (b : Bool) (ys bs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .restore) v ys (b::bs) []) =
      some (saddCfg (some .restore) {v with first := some b} (xor b v.left :: ys) bs []) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_restore_nil (v : SAddState) (ys : List Bool) :
    signedAdditionMachine.step (saddCfg (some .restore) v ys [] []) =
      some (saddCfg none saddInitial (Complexity.BitEncoding.frame [v.left]++ys) [] []) := by
  simp [signedAdditionMachine,saddFinish,saddCfg,Complexity.BitEncoding.frame,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_trim_nil (v : SAddState) :
    signedAdditionMachine.step (saddCfg (some .trim) v [] [] []) =
      some (saddCfg none saddInitial (Complexity.BitEncoding.frame [v.left]) [] []) := by
  simp [signedAdditionMachine,saddFinish,saddCfg,Complexity.BitEncoding.frame,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_trim_false (v : SAddState) (b : Bool) (bs : List Bool) (hb : xor b v.left=false) :
    signedAdditionMachine.step (saddCfg (some .trim) v [] (b::bs) []) =
      some (saddCfg (some .trim) {v with first := some b} [] bs []) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux,hb]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_trim_true (v : SAddState) (b : Bool) (bs : List Bool) (hb : xor b v.left=true) :
    signedAdditionMachine.step (saddCfg (some .trim) v [] (b::bs) []) =
      some (saddCfg (some .restore) {v with first := some b} [true] bs []) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux,hb]
  funext k; rcases k with _ | (_ | _) <;> simp

@[simp] theorem sadd_step_finish (v : SAddState) (bs : List Bool) :
    signedAdditionMachine.step (saddCfg (some .add) v [] bs []) =
      some (saddCfg (some .trim) {saddInitial with left := (fullAdderBit v.left v.right
        (fullAdderCarry v.left v.right v.carry))} [] (fullAdderBit v.left v.right v.carry :: bs) []) := by
  simp [signedAdditionMachine,saddCfg,step,stepAux]
  funext k; rcases k with _ | (_ | _) <;> simp

theorem sadd_step_add (v : SAddState) (xs ys bs : List Bool) (h : xs≠[] ∨ ys≠[]) :
    signedAdditionMachine.step (saddCfg (some .add) v ys bs xs) =
      some (saddCfg (some .add)
        {v with carry := (fullAdderCarry (xor (xs.head?.getD false) v.left)
          (xor (ys.head?.getD false) v.right) v.carry), first := none, second := none}
        ys.tail (fullAdderBit (xor (xs.head?.getD false) v.left)
          (xor (ys.head?.getD false) v.right) v.carry :: bs) xs.tail) := by
  cases xs with
  | nil =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp [signedAdditionMachine,saddCfg,step,stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
  | cons x xs =>
    cases ys with
    | nil =>
      simp [signedAdditionMachine,saddCfg,step,stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp
    | cons y ys =>
      simp [signedAdditionMachine,saddCfg,step,stepAux]
      funext k; rcases k with _ | (_ | _) <;> simp

def sadd_parse (v : SAddState) (as ys bs xs : List Bool) :
    EvalsToInTime signedAdditionMachine.step
      (saddCfg (some .parse) v (Complexity.BitEncoding.frame as ++ ys) bs xs)
      (some (saddCfg (some .rightHeader) {v with first := some false} ys (as.reverse++bs) xs)) (as.length+1) := by
  induction as generalizing v bs with
  | nil => simpa [Complexity.BitEncoding.frame] using oneStep signedAdditionMachine.step (sadd_step_parse_end v ys bs xs)
  | cons b as ih =>
    have h := EvalsToInTime.trans signedAdditionMachine.step 1 (as.length+1) _ _ _
      (oneStep signedAdditionMachine.step (sadd_step_parse_bit v b (Complexity.BitEncoding.frame as++ys) bs xs))
      (ih {v with first := some b} (b::bs))
    simpa [Complexity.BitEncoding.frame,List.reverse_cons,List.append_assoc] using h

def sadd_reverse (v : SAddState) (ys bs xs : List Bool) :
    EvalsToInTime signedAdditionMachine.step (saddCfg (some .reverse) v ys bs xs)
      (some (saddCfg (some .add) (saddFlags v.left v.right) ys [] (bs.reverse++xs))) (bs.length+1) := by
  induction bs generalizing v xs with
  | nil => simpa using oneStep signedAdditionMachine.step (sadd_step_reverse_nil v ys xs)
  | cons b bs ih =>
    have h := EvalsToInTime.trans signedAdditionMachine.step 1 (bs.length+1) _ _ _
      (oneStep signedAdditionMachine.step (sadd_step_reverse_cons v b ys bs xs))
      (ih {v with first := some b} (b::xs))
    simpa [List.reverse_cons,List.append_assoc] using h

def sadd_restore (v : SAddState) (ys bs : List Bool) :
    EvalsToInTime signedAdditionMachine.step (saddCfg (some .restore) v ys bs [])
      (some (saddCfg none saddInitial
        (Complexity.BitEncoding.frame [v.left] ++ bs.reverse.map (fun b => xor b v.left) ++ ys) [] [])) (bs.length+1) := by
  induction bs generalizing v ys with
  | nil => simpa using oneStep signedAdditionMachine.step (sadd_step_restore_nil v ys)
  | cons b bs ih =>
    have h := EvalsToInTime.trans signedAdditionMachine.step 1 (bs.length+1) _ _ _
      (oneStep signedAdditionMachine.step (sadd_step_restore_cons v b ys bs))
      (ih {v with first := some b} (xor b v.left :: ys))
    simpa [List.reverse_cons,List.map_append,List.append_assoc] using h

def sadd_trim (v : SAddState) (bs : List Bool) :
    EvalsToInTime signedAdditionMachine.step (saddCfg (some .trim) v [] bs [])
      (some (saddCfg none saddInitial (intWordOutput v.left bs.reverse) [] [])) (bs.length+1) := by
  induction bs generalizing v with
  | nil => simpa [intWordOutput,normalizeBits] using oneStep signedAdditionMachine.step (sadd_step_trim_nil v)
  | cons b bs ih =>
    cases hb : xor b v.left with
    | false =>
      have h := EvalsToInTime.trans signedAdditionMachine.step 1 (bs.length+1) _ _ _
        (oneStep signedAdditionMachine.step (sadd_step_trim_false v b bs hb))
        (ih {v with first := some b})
      simpa [intWordOutput,List.reverse_cons,List.map_append,hb] using h
    | true =>
      have h := EvalsToInTime.trans signedAdditionMachine.step 1 (bs.length+1) _ _ _
        (oneStep signedAdditionMachine.step (sadd_step_trim_true v b bs hb))
        (sadd_restore {v with first := some b} [true] bs)
      simpa [intWordOutput,List.reverse_cons,List.map_append,hb] using h

/-- Signed full-adder execution, including sign extension and canonical output. -/
def sadd_run (v : SAddState) (xs ys bs : List Bool) :
    EvalsToInTime signedAdditionMachine.step (saddCfg (some .add) v ys bs xs)
      (some (saddCfg none saddInitial (intWordOutput (twosAdd v.left v.right v.carry xs ys).1
        (bs.reverse ++ (twosAdd v.left v.right v.carry xs ys).2)) [] []))
      (2*(xs.length+ys.length)+bs.length+3) := by
  by_cases h : xs=[] ∧ ys=[]
  · rcases h with ⟨rfl,rfl⟩
    have he := EvalsToInTime.trans signedAdditionMachine.step 1
      ((fullAdderBit v.left v.right v.carry :: bs).length+1) _ _ _
      (oneStep signedAdditionMachine.step (sadd_step_finish v bs))
      (sadd_trim {saddInitial with left := (fullAdderBit v.left v.right
        (fullAdderCarry v.left v.right v.carry))} (fullAdderBit v.left v.right v.carry :: bs))
    simpa [twosAdd,List.reverse_cons,Nat.add_assoc] using he
  · have hn : xs≠[] ∨ ys≠[] := by tauto
    let bit := fullAdderBit (xor (xs.head?.getD false) v.left) (xor (ys.head?.getD false) v.right) v.carry
    let c := fullAdderCarry (xor (xs.head?.getD false) v.left) (xor (ys.head?.getD false) v.right) v.carry
    let v' := {v with carry := c,first := none,second := none}
    have hs := sadd_step_add v xs ys bs hn
    have he := EvalsToInTime.trans signedAdditionMachine.step 1
      (2*(xs.tail.length+ys.tail.length)+(bit::bs).length+3) _ _ _
      (oneStep signedAdditionMachine.step hs) (sadd_run v' xs.tail ys.tail (bit::bs))
    have hout : intWordOutput (twosAdd v'.left v'.right v'.carry xs.tail ys.tail).1
        ((bit::bs).reverse ++ (twosAdd v'.left v'.right v'.carry xs.tail ys.tail).2) =
        intWordOutput (twosAdd v.left v.right v.carry xs ys).1
          (bs.reverse ++ (twosAdd v.left v.right v.carry xs ys).2) := by
      rw [twosAdd_step v.left v.right v.carry xs ys hn]
      simp [v',c,bit,List.reverse_cons,List.append_assoc]
    rw [hout] at he
    apply weakenTime he
    have hl : xs.tail.length+ys.tail.length+1≤xs.length+ys.length := by
      cases xs <;> cases ys <;> simp_all
      omega
    simp only [List.length_cons]
    omega
termination_by xs.length+ys.length
decreasing_by
  have hn : xs≠[] ∨ ys≠[] := by tauto
  cases xs <;> cases ys <;> simp_all
  omega

def intPairWord (sa sb : Bool) (xs ys : List Bool) : List Bool :=
  [true,true,true,sa,true,false] ++ Complexity.BitEncoding.frame xs ++ [true,sb,false] ++ ys

/-- Exact framed-pair input identity for the signed-index integer codec. -/
theorem intPairWord_encode (sa sb : Bool) (a b : ℕ) :
    (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.int).encode
      (signedIndex sa a,signedIndex sb b) = intPairWord sa sb (Computability.encodeNat a) (Computability.encodeNat b) := by
  cases sa <;> cases sb <;> simp [intPairWord,Complexity.BitEncoding.prod,Complexity.BitEncoding.int,
    Complexity.BitEncoding.retract,Complexity.BitEncoding.bool,Complexity.BitEncoding.nat,Complexity.BitEncoding.frame,signedIndex,List.append_assoc]

def signedAddition_outputs (sa sb : Bool) (a b : ℕ) :
    TM2OutputsInTime signedAdditionMachine
      ((Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.int).encode
        (signedIndex sa a,signedIndex sb b))
      (some (Complexity.BitEncoding.int.encode (signedIndex sa a+signedIndex sb b)))
      (2*((Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.int).encode
        (signedIndex sa a,signedIndex sb b)).length) := by
  let xs := Computability.encodeNat a
  let ys := Computability.encodeNat b
  have h1 := oneStep signedAdditionMachine.step
    (sadd_step_header saddInitial sa (Complexity.BitEncoding.frame xs ++ ([true,sb,false] ++ ys)) [] [])
  have h2 := sadd_parse {saddInitial with left := sa} xs ([true,sb,false]++ys) [] []
  have h3 := oneStep signedAdditionMachine.step
    (sadd_step_rightHeader {saddInitial with left := sa,first := some false} sb ys xs.reverse [])
  have h4 := sadd_reverse (saddFlags sa sb) ys xs.reverse []
  have h5 := sadd_run (saddFlags sa sb) xs ys []
  simp only [List.reverse_reverse,List.reverse_nil,List.nil_append,List.length_reverse,
    List.append_nil,List.length_nil,Nat.add_zero] at h2 h4 h5
  have h45 := EvalsToInTime.trans signedAdditionMachine.step (xs.length+1)
    (2*(xs.length+ys.length)+3) _ _ _ h4 h5
  have h345 := EvalsToInTime.trans signedAdditionMachine.step 1
    ((2*(xs.length+ys.length)+3)+(xs.length+1)) _ _ _ h3 h45
  have h2345 := EvalsToInTime.trans signedAdditionMachine.step (xs.length+1)
    (((2*(xs.length+ys.length)+3)+(xs.length+1))+1) _ _ _ h2 h345
  have h := EvalsToInTime.trans signedAdditionMachine.step 1
    ((((2*(xs.length+ys.length)+3)+(xs.length+1))+1)+(xs.length+1)) _ _ _ h1 h2345
  have hout := intWordOutput_add_encode sa sb a b
  change intWordOutput (twosAdd sa sb false xs ys).1 (twosAdd sa sb false xs ys).2 = _ at hout
  simp only [saddFlags] at h
  rw [hout] at h
  have hi : initList signedAdditionMachine (intPairWord sa sb xs ys) =
      saddCfg (some .header) saddInitial (intPairWord sa sb xs ys) [] [] := by
    unfold initList saddCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  have ho (out : List Bool) : haltList signedAdditionMachine out = saddCfg none saddInitial out [] [] := by
    unfold haltList saddCfg
    congr 1
    funext k; rcases k with _ | (_ | _) <;> rfl
  rw [intPairWord_encode]
  change EvalsToInTime signedAdditionMachine.step (initList signedAdditionMachine (intPairWord sa sb xs ys))
    (some (haltList signedAdditionMachine (Complexity.BitEncoding.int.encode (signedIndex sa a+signedIndex sb b)))) _
  rw [hi,ho]
  apply weakenTime (by simpa only [intPairWord,List.append_assoc] using h)
  change _ ≤ 2*(intPairWord sa sb xs ys).length
  simp only [intPairWord,List.length_append,Complexity.BitEncoding.frame_length,List.length_cons,List.length_nil]
  omega

noncomputable def signedAdditionComputable :
    TM2ComputableInPolyTime
      (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.int).toFinEncoding
      Complexity.BitEncoding.int.toFinEncoding (fun p : ℤ×ℤ => p.1+p.2) where
  tm := signedAdditionMachine
  inputAlphabet := Equiv.refl Bool
  outputAlphabet := Equiv.refl Bool
  time := Polynomial.C 2*Polynomial.X
  outputsFun p := by
    rcases p with ⟨a,b⟩
    cases a with
    | ofNat a =>
      cases b with
      | ofNat b => simpa [Complexity.BitEncoding.toFinEncoding,signedIndex,Polynomial.eval_mul,Equiv.refl,Equiv.symm] using signedAddition_outputs false false a b
      | negSucc b => simpa [Complexity.BitEncoding.toFinEncoding,signedIndex,Polynomial.eval_mul,Equiv.refl,Equiv.symm] using signedAddition_outputs false true a b
    | negSucc a =>
      cases b with
      | ofNat b => simpa [Complexity.BitEncoding.toFinEncoding,signedIndex,Polynomial.eval_mul,Equiv.refl,Equiv.symm] using signedAddition_outputs true false a b
      | negSucc b => simpa [Complexity.BitEncoding.toFinEncoding,signedIndex,Polynomial.eval_mul,Equiv.refl,Equiv.symm] using signedAddition_outputs true true a b

theorem fp_integer_addition :
    Complexity.FP (Complexity.BitEncoding.prod Complexity.BitEncoding.int Complexity.BitEncoding.int)
      Complexity.BitEncoding.int (fun p : ℤ×ℤ => p.1+p.2) := ⟨signedAdditionComputable⟩

end PlanarHom.BinaryArithmetic
