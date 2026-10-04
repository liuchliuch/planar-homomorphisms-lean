import PlanarHom.ListMutationMachines
import PlanarHom.OracleSubstitutionOnTrace
import PlanarHom.OracleReductionComposition
import Mathlib.Tactic.Linarith

/-! # An actual typed list-map machine with canonical framing and on-trace substitution -/
namespace PlanarHom.ListMapMachines
open Turing Turing.TM2 Complexity MachineComposition

inductive Stack | input | output | work | query deriving DecidableEq,Fintype
inductive Label | header | check | parse | prepare | query | answer | finish deriving DecidableEq,Fintype
abbrev State := Unit×Option Bool
abbrev Statement := Stmt (fun _ : Stack => Bool) Label State

def store (input output work query : Bits) : Stack→Bits
  | .input => input | .output => output | .work => work | .query => query

def goto (l : Label) : Statement := .load (fun _ => ((),none)) (.goto (fun _ => l))

def program : Label→Statement
  | .header => .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.getD false)
      (.pop .input (fun v b => (v.1,b)) <| .push .output (fun _ => true) <|
        .push .output (fun v => v.2.getD false) (goto .header))
      (.push .output (fun _ => false) (goto .check))
  | .check => .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .input (fun v => v.2.getD false) (goto .parse)) (goto .finish)
  | .parse => .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.getD false)
      (.pop .input (fun v b => (v.1,b)) <| .push .work (fun v => v.2.getD false) (goto .parse))
      (goto .prepare)
  | .prepare => .pop .work (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .query (fun v => v.2.getD false) (goto .prepare)) (goto .query)
  | .query => .halt
  | .answer => .pop .query (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .output (fun _ => true) <| .push .output (fun v => v.2.getD false) (goto .answer))
      (.push .output (fun _ => false) (goto .check))
  | .finish => .pop .output (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .input (fun v => v.2.getD false) (goto .finish)) (.load (fun _ => ((),none)) .halt)

def machine : OracleTM2 where
  core := {
    tm := {
      K := Stack
      Γ := fun _ => Bool
      k₀ := .input
      k₁ := .input
      Λ := Label
      main := .header
      σ := State
      initialState := ((),none)
      Γk₀Fin := inferInstance
      m := program }
    inputAlphabet:=Equiv.refl Bool
    outputAlphabet:=Equiv.refl Bool }
  finiteAlphabet := fun _ => inferInstance
  queryStack := .query
  answerStack := .query
  queryAlphabet := Equiv.refl Bool
  answerAlphabet := Equiv.refl Bool
  request | .query => some .answer | _ => none

def cfg (l : Label) (xs out work query : Bits) : machine.Cfg :=
  ⟨some l,((),none),store xs out work query⟩

def typedOracle {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (q : Bits) : Bits :=
  match ea.decode q with | none => [] | some a => eb.encode (f a)

@[simp] theorem typedOracle_encode {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (a : α) :
    typedOracle ea eb f (ea.encode a)=eb.encode (f a) := by simp [typedOracle,ea.decode_encode]

def Good {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (qa : Bits×Bits) : Prop :=
  ∃ a,qa=(ea.encode a,eb.encode (f a))

def Runs {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β)
    (c d : machine.Cfg) (bound : ℕ) : Prop :=
  ∃s t qs,machine.Run (typedOracle ea eb f) c d s t qs ∧ t≤bound ∧ ∀qa∈qs,Good ea eb f qa

variable {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β} {f : α→β}

theorem Runs.trans {c d z : machine.Cfg} {n k : ℕ}
    (h : Runs ea eb f c d n) (h' : Runs ea eb f d z k) : Runs ea eb f c z (n+k) := by
  obtain ⟨s,t,qs,hr,ht,hgood⟩ := h
  obtain ⟨s',t',qs',hr',ht',hgood'⟩ := h'
  refine ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht',?_⟩
  intro qa ha
  rcases List.mem_append.mp ha with ha|ha
  · exact hgood qa ha
  · exact hgood' qa ha

theorem Runs.mono {c d : machine.Cfg} {n k : ℕ} (h : Runs ea eb f c d n) (hk : n≤k) : Runs ea eb f c d k := by
  obtain ⟨s,t,qs,hr,ht,hgood⟩ := h
  exact ⟨s,t,qs,hr,ht.trans hk,hgood⟩

theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c=none)
    (hs : machine.core.tm.step c=some d) : Runs ea eb f c d 1 :=
  ⟨1,1,[],.ordinary hn hs (.refl d),by rfl,by simp⟩

private theorem header_bit (b : Bool) (xs out : Bits) :
    Runs ea eb f (cfg .header (true::b::xs) out [] []) (cfg .header xs (b::true::out) [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem header_end (xs out : Bits) :
    Runs ea eb f (cfg .header (false::xs) out [] []) (cfg .check xs (false::out) [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem header_run (h xs out : Bits) :
    Runs ea eb f (cfg .header (BitEncoding.frame h++xs) out [] [])
      (cfg .check xs ((BitEncoding.frame h).reverse++out) [] []) (h.length+1) := by
  induction h generalizing out with
  | nil => simpa [BitEncoding.frame] using (header_end (ea:=ea) (eb:=eb) (f:=f) xs out)
  | cons b h ih =>
    have he := (header_bit (ea:=ea) (eb:=eb) (f:=f) b (BitEncoding.frame h++xs) out).trans (ih (b::true::out))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem check_more (b : Bool) (xs out : Bits) :
    Runs ea eb f (cfg .check (b::xs) out [] []) (cfg .parse (b::xs) out [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]

private theorem check_end (out : Bits) :
    Runs ea eb f (cfg .check [] out [] []) (cfg .finish [] out [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]

private theorem parse_bit (b : Bool) (xs out work : Bits) :
    Runs ea eb f (cfg .parse (true::b::xs) out work []) (cfg .parse xs out (b::work) []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem parse_end (xs out work : Bits) :
    Runs ea eb f (cfg .parse (false::xs) out work []) (cfg .prepare xs out work []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem parse_run (w xs out work : Bits) :
    Runs ea eb f (cfg .parse (BitEncoding.frame w++xs) out work [])
      (cfg .prepare xs out (w.reverse++work) []) (w.length+1) := by
  induction w generalizing work with
  | nil => simpa [BitEncoding.frame] using (parse_end (ea:=ea) (eb:=eb) (f:=f) xs out work)
  | cons b w ih =>
    have he := (parse_bit (ea:=ea) (eb:=eb) (f:=f) b (BitEncoding.frame w++xs) out work).trans (ih (b::work))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem prepare_bit (b : Bool) (xs out work query : Bits) :
    Runs ea eb f (cfg .prepare xs out (b::work) query) (cfg .prepare xs out work (b::query)) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem prepare_end (xs out query : Bits) :
    Runs ea eb f (cfg .prepare xs out [] query) (cfg .query xs out [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]

theorem prepare_run (xs out work query : Bits) :
    Runs ea eb f (cfg .prepare xs out work query) (cfg .query xs out [] (work.reverse++query)) (work.length+1) := by
  induction work generalizing query with
  | nil => simpa using (prepare_end (ea:=ea) (eb:=eb) (f:=f) xs out query)
  | cons b work ih =>
    have he := (prepare_bit (ea:=ea) (eb:=eb) (f:=f) b xs out work query).trans (ih (b::query))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem answer_bit (b : Bool) (xs out query : Bits) :
    Runs ea eb f (cfg .answer xs out [] (b::query)) (cfg .answer xs (b::true::out) [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem answer_end (xs out : Bits) :
    Runs ea eb f (cfg .answer xs out [] []) (cfg .check xs (false::out) [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem answer_run (xs out query : Bits) :
    Runs ea eb f (cfg .answer xs out [] query)
      (cfg .check xs ((BitEncoding.frame query).reverse++out) [] []) (query.length+1) := by
  induction query generalizing out with
  | nil => simpa [BitEncoding.frame] using (answer_end (ea:=ea) (eb:=eb) (f:=f) xs out)
  | cons b query ih =>
    have he := (answer_bit (ea:=ea) (eb:=eb) (f:=f) b xs out query).trans (ih (b::true::out))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem finish_bit (b : Bool) (xs out : Bits) :
    Runs ea eb f (cfg .finish xs (b::out) [] []) (cfg .finish (b::xs) out [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem finish_end (xs : Bits) :
    Runs ea eb f (cfg .finish xs [] [] []) (machine.final xs) 1 := by
  apply ordinary rfl
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,program,stepAux,store,OracleTM2.final,haltList,Equiv.refl]

theorem finish_run (xs out : Bits) :
    Runs ea eb f (cfg .finish xs out [] []) (machine.final (out.reverse++xs)) (out.length+1) := by
  induction out generalizing xs with
  | nil => simpa using (finish_end (ea:=ea) (eb:=eb) (f:=f) xs)
  | cons b out ih =>
    have he := (finish_bit (ea:=ea) (eb:=eb) (f:=f) b xs out).trans (ih (b::xs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

theorem query_run (a : α) (xs out : Bits) :
    Runs ea eb f (cfg .query xs out [] (ea.encode a)) (cfg .answer xs out [] (eb.encode (f a)))
      (1+(ea.encode a).length+(eb.encode (f a)).length) := by
  have hq : machine.continuation (cfg .query xs out [] (ea.encode a))=some .answer := rfl
  have hw : machine.queryWord (cfg .query xs out [] (ea.encode a))=ea.encode a := by
    simp [machine,OracleTM2.queryWord,cfg,store,Equiv.refl]
  have he : machine.answerCfg (typedOracle ea eb f) (cfg .query xs out [] (ea.encode a)) .answer =
      cfg .answer xs out [] (eb.encode (f a)) := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,store]
      funext k; cases k <;> rfl
  refine ⟨1,_,[(ea.encode a,eb.encode (f a))],?_,Nat.le_refl _,?_⟩
  · have h := OracleTM2.Run.query (m:=machine) (oracle:=typedOracle ea eb f) Label.answer hq
      (OracleTM2.Run.refl (machine.answerCfg (typedOracle ea eb f) (cfg .query xs out [] (ea.encode a)) .answer))
    simpa only [he,hw,Nat.zero_add,typedOracle_encode] using h
  · intro qa ha
    exact ⟨a,List.mem_singleton.mp ha⟩

private theorem check_frame (w xs out : Bits) :
    Runs ea eb f (cfg .check (BitEncoding.frame w++xs) out [] [])
      (cfg .parse (BitEncoding.frame w++xs) out [] []) 1 := by
  cases w with
  | nil => exact check_more false xs out
  | cons b w => exact check_more true (b::(BitEncoding.frame w++xs)) out

def itemCost (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (a : α) : ℕ :=
  3*(ea.encode a).length+2*(eb.encode (f a)).length+5

def mapCost (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (xs : List α) : ℕ :=
  (xs.map (itemCost ea eb f)).sum

/-- Every oracle call in the complete loop is exactly an encoded list element. -/
theorem loop_run (xs : List α) (out : Bits) :
    Runs ea eb f (cfg .check (BitEncoding.frames (xs.map ea.encode)) out [] [])
      (cfg .finish [] ((BitEncoding.frames ((xs.map f).map eb.encode)).reverse++out) [] [])
      (mapCost ea eb f xs+1) := by
  induction xs generalizing out with
  | nil => simpa [BitEncoding.frames,mapCost] using (check_end (ea:=ea) (eb:=eb) (f:=f) out)
  | cons a xs ih =>
    let rest := BitEncoding.frames (xs.map ea.encode)
    have h₁ := check_frame (ea:=ea) (eb:=eb) (f:=f) (ea.encode a) rest out
    have h₂ := parse_run (ea:=ea) (eb:=eb) (f:=f) (ea.encode a) rest out []
    have h₃ := prepare_run (ea:=ea) (eb:=eb) (f:=f) rest out (ea.encode a).reverse []
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₂ h₃
    have h₄ := query_run (ea:=ea) (eb:=eb) (f:=f) a rest out
    have h₅ := answer_run (ea:=ea) (eb:=eb) (f:=f) rest out (eb.encode (f a))
    have h := ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans
      (ih ((BitEncoding.frame (eb.encode (f a))).reverse++out))
    convert h using 1
    · simp [BitEncoding.frames,List.reverse_append,List.append_assoc]
    · simp [mapCost,itemCost]
      ring

def mapTime (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (xs : List α) : ℕ :=
  (BitEncoding.nat.encode xs.length).length + mapCost ea eb f xs + (eb.list.encode (xs.map f)).length + 3

/-- The original canonical length header is preserved verbatim; every mapped
item is separately framed and all four caller stacks are cleared at halt. -/
theorem run (xs : List α) :
    Runs ea eb f (machine.initial (ea.list.encode xs)) (machine.final (eb.list.encode (xs.map f)))
      (mapTime ea eb f xs) := by
  let header := BitEncoding.frame (BitEncoding.nat.encode xs.length)
  let output := BitEncoding.frames ((xs.map f).map eb.encode)
  have h₁ := header_run (ea:=ea) (eb:=eb) (f:=f) (BitEncoding.nat.encode xs.length)
    (BitEncoding.frames (xs.map ea.encode)) []
  simp only [List.append_nil] at h₁
  have h₂ := loop_run (ea:=ea) (eb:=eb) (f:=f) xs header.reverse
  have h₃ := finish_run (ea:=ea) (eb:=eb) (f:=f) [] (output.reverse++header.reverse)
  have h := (h₁.trans h₂).trans h₃
  have hi : machine.initial (ea.list.encode xs) =
      cfg .header (header++BitEncoding.frames (xs.map ea.encode)) [] [] [] := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,OracleTM2.initial,initList,cfg,store,BitEncoding.list,Equiv.refl,header]
  rw [hi]
  convert h using 1
  · simp [BitEncoding.list,output,header,List.reverse_append]
  · simp only [mapTime,header,output,List.length_append,List.length_reverse,
      BitEncoding.list,List.length_map]
    omega

theorem mem_le_sum_map {γ : Type} (g : γ→ℕ) {xs : List γ} {a : γ} (ha : a∈xs) :
    g a ≤ (xs.map g).sum := by
  induction xs with
  | nil => simp at ha
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with rfl|ha
    · simp
    · simpa using (ih ha).trans (Nat.le_add_left _ (g b))

theorem sum_map_le_mul {γ : Type} (g : γ→ℕ) (xs : List γ) (M : ℕ) (h : ∀a∈xs,g a≤M) :
    (xs.map g).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha := h a (by simp)
    have ht := ih (fun b hb => h b (by simp [hb]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith

/-- A polynomial source-oracle cost follows solely from the callee's actual
output-length polynomial and the serialized input size. -/
theorem mapTime_bound (body : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f)
    (xs : List α) : mapTime ea eb f xs ≤
      ((Polynomial.C 4*Polynomial.X+Polynomial.C 4)*
        (Polynomial.X+outputLengthPolynomial body+Polynomial.C 4)).eval (ea.list.encode xs).length := by
  let N := (ea.list.encode xs).length
  let P := (outputLengthPolynomial body).eval N
  let I := (xs.map (fun a => (ea.encode a).length)).sum
  have hN : N=2*(BitEncoding.nat.encode xs.length).length+1+2*I+xs.length := by
    simp [N,I,BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hn : xs.length≤N := by omega
  have hi : I≤N := by omega
  have hinput (a : α) (ha : a∈xs) : (ea.encode a).length≤N :=
    (mem_le_sum_map (fun a => (ea.encode a).length) ha).trans hi
  have hout (a : α) (ha : a∈xs) : (eb.encode (f a)).length≤P := by
    exact (encoded_output_length_le body a).trans (natPolynomial_monotone _ (hinput a ha))
  have hcost : mapCost ea eb f xs≤N*(3*N+2*P+5) := by
    apply (sum_map_le_mul (itemCost ea eb f) xs (3*N+2*P+5) (fun a ha => ?_)).trans
      (Nat.mul_le_mul_right _ hn)
    have hia := hinput a ha
    have hoa := hout a ha
    dsimp [itemCost]
    omega
  have hsum : (xs.map (fun a => (eb.encode (f a)).length)).sum≤N*P :=
    (sum_map_le_mul (fun a => (eb.encode (f a)).length) xs P hout).trans (Nat.mul_le_mul_right P hn)
  have houtput : (eb.list.encode (xs.map f)).length ≤ N+2*N*P := by
    simp only [BitEncoding.list,List.length_append,BitEncoding.frame_length,List.length_map,
      BitEncoding.frames_length,List.map_map,Function.comp_def]
    nlinarith
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
  change mapTime ea eb f xs≤(4*N+4)*(N+P+4)
  dsimp [mapTime]
  nlinarith

/-- Actual map compiler. Only the canonical query words proved in `run` are
required to terminate; no behavior is assumed on malformed callee inputs. -/
noncomputable def computer (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β)
    (body : TM2ComputableInPolyTime ea.toFinEncoding eb.toFinEncoding f) :
    TM2ComputableInPolyTime ea.list.toFinEncoding eb.list.toFinEncoding (List.map f) := by
  let time : Polynomial ℕ := (Polynomial.C 4*Polynomial.X+Polynomial.C 4)*
    (Polynomial.X+outputLengthPolynomial body+Polynomial.C 4)
  let g := body.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine time body.time
    outputsFun := ?_ }
  intro xs
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩ := run (ea:=ea) (eb:=eb) (f:=f) xs
  have hN : ∀k,((machine.initial (ea.list.encode xs)).stk k).length≤(ea.list.encode xs).length :=
    OracleReductionComposition.initial_length machine _
  have hc : cost≤time.eval (ea.list.encode xs).length := hcost.trans (mapTime_bound body xs)
  obtain ⟨t,ht,he⟩ := OracleSubstitution.compiled_run_on_trace machine g hr body.time
    (fun q a hqa => by
      apply Classical.choice
      obtain ⟨x,hx⟩ := hgood (q,a) hqa
      have hq := congrArg Prod.fst hx
      have ha := congrArg Prod.snd hx
      dsimp only at hq ha
      subst q; subst a
      exact ⟨body.outputsFun x⟩) _ hN
  refine ⟨{steps:=t,evals_in_steps:=?_,steps_le_m:=?_}⟩
  · rw [OracleSubstitution.idle_initial,OracleSubstitution.idle_final] at he
    exact he
  · exact ht.trans (OracleReductionComposition.bound_polynomial machine time body.time
      (ea.list.encode xs).length cost hc)

theorem fp_map (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β) (hf : FP ea eb f) :
    FP ea.list eb.list (List.map f) := by
  obtain ⟨body⟩ := hf
  exact ⟨computer ea eb f body⟩

end PlanarHom.ListMapMachines
