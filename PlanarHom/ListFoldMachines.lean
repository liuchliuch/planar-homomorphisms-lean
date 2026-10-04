import PlanarHom.ListMapMachines

/-! # Actual polynomially bounded typed left folds -/
namespace PlanarHom.ListFoldMachines
open Turing Turing.TM2 Complexity MachineComposition

inductive Stack | input | acc | work | query deriving DecidableEq,Fintype
inductive Label | initParse | initReverse | header | check | parse | prepare | frame | prefix
  | query | answer | restore | finish | emit deriving DecidableEq,Fintype
abbrev State := Unit×Option Bool
abbrev Statement := Stmt (fun _ : Stack => Bool) Label State

def store (input acc work query : Bits) : Stack→Bits
  | .input => input | .acc => acc | .work => work | .query => query

def goto (l : Label) : Statement := .load (fun _ => ((),none)) (.goto (fun _ => l))
def transfer (source target : Stack) (loop next : Label) : Statement :=
  .pop source (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
    (.push target (fun v => v.2.getD false) (goto loop)) (goto next)
def parse (loop next : Label) : Statement :=
  .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.getD false)
    (.pop .input (fun v b => (v.1,b)) <| .push .work (fun v => v.2.getD false) (goto loop)) (goto next)

def program : Label→Statement
  | .initParse => parse .initParse .initReverse
  | .initReverse => transfer .work .acc .initReverse .header
  | .header => .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.getD false)
      (.pop .input (fun v b => (v.1,b)) (goto .header)) (goto .check)
  | .check => .pop .input (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .input (fun v => v.2.getD false) (goto .parse)) (goto .finish)
  | .parse => parse .parse .prepare
  | .prepare => transfer .work .query .prepare .frame
  | .frame => .pop .acc (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .work (fun _ => true) <| .push .work (fun v => v.2.getD false) (goto .frame))
      (.push .work (fun _ => false) (goto .prefix))
  | .prefix => transfer .work .query .prefix .query
  | .query => .halt
  | .answer => transfer .query .work .answer .restore
  | .restore => transfer .work .acc .restore .check
  | .finish => transfer .acc .work .finish .emit
  | .emit => .pop .work (fun v b => (v.1,b)) <| .branch (fun v => v.2.isSome)
      (.push .input (fun v => v.2.getD false) (goto .emit)) (.load (fun _ => ((),none)) .halt)

def machine : OracleTM2 where
  core := {
    tm := {
      K := Stack
      Γ := fun _ => Bool
      k₀ := .input
      k₁ := .input
      Λ := Label
      main := .initParse
      σ := State
      initialState := ((),none)
      Γk₀Fin := inferInstance
      m := program }
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool }
  finiteAlphabet := fun _ => inferInstance
  queryStack := .query
  answerStack := .query
  queryAlphabet := Equiv.refl Bool
  answerAlphabet := Equiv.refl Bool
  request | .query => some .answer | _ => none

def cfg (l : Label) (xs acc work query : Bits) : machine.Cfg :=
  ⟨some l,((),none),store xs acc work query⟩

variable {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β} {f : β→α→β}

def oracle (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β) :=
  ListMapMachines.typedOracle (eb.prod ea) eb (fun p => f p.1 p.2)

def Runs (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β)
    (c d : machine.Cfg) (bound : ℕ) : Prop :=
  ∃s t qs,machine.Run (oracle ea eb f) c d s t qs ∧ t≤bound ∧
    ∀qa∈qs,ListMapMachines.Good (eb.prod ea) eb (fun p => f p.1 p.2) qa

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

private theorem initReverse_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .initReverse xs acc (b::work) query) (cfg .initReverse xs (b::acc) work query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem initReverse_end (xs acc query : Bits) :
    Runs ea eb f (cfg .initReverse xs acc [] query) (cfg .header xs acc [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem initReverse_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .initReverse xs acc work query) (cfg .header xs (work.reverse++acc) [] query) (work.length+1) := by
  induction work generalizing acc with
  | nil => simpa using (initReverse_end (ea:=ea) (eb:=eb) (f:=f) xs acc query)
  | cons b work ih =>
    have he := (initReverse_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::acc))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem prepare_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .prepare xs acc (b::work) query) (cfg .prepare xs acc work (b::query)) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem prepare_end (xs acc query : Bits) :
    Runs ea eb f (cfg .prepare xs acc [] query) (cfg .frame xs acc [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem prepare_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .prepare xs acc work query) (cfg .frame xs acc [] (work.reverse++query)) (work.length+1) := by
  induction work generalizing query with
  | nil => simpa using (prepare_end (ea:=ea) (eb:=eb) (f:=f) xs acc query)
  | cons b work ih =>
    have he := (prepare_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::query))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem prefix_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .prefix xs acc (b::work) query) (cfg .prefix xs acc work (b::query)) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem prefix_end (xs acc query : Bits) :
    Runs ea eb f (cfg .prefix xs acc [] query) (cfg .query xs acc [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem prefix_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .prefix xs acc work query) (cfg .query xs acc [] (work.reverse++query)) (work.length+1) := by
  induction work generalizing query with
  | nil => simpa using (prefix_end (ea:=ea) (eb:=eb) (f:=f) xs acc query)
  | cons b work ih =>
    have he := (prefix_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::query))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem answer_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .answer xs acc work (b::query)) (cfg .answer xs acc (b::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem answer_end (xs acc work : Bits) :
    Runs ea eb f (cfg .answer xs acc work []) (cfg .restore xs acc work []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem answer_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .answer xs acc work query) (cfg .restore xs acc (query.reverse++work) []) (query.length+1) := by
  induction query generalizing work with
  | nil => simpa using (answer_end (ea:=ea) (eb:=eb) (f:=f) xs acc work)
  | cons b query ih =>
    have he := (answer_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::work))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem restore_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .restore xs acc (b::work) query) (cfg .restore xs (b::acc) work query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem restore_end (xs acc query : Bits) :
    Runs ea eb f (cfg .restore xs acc [] query) (cfg .check xs acc [] query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem restore_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .restore xs acc work query) (cfg .check xs (work.reverse++acc) [] query) (work.length+1) := by
  induction work generalizing acc with
  | nil => simpa using (restore_end (ea:=ea) (eb:=eb) (f:=f) xs acc query)
  | cons b work ih =>
    have he := (restore_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::acc))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem finish_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .finish xs (b::acc) work query) (cfg .finish xs acc (b::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem finish_end (xs work query : Bits) :
    Runs ea eb f (cfg .finish xs [] work query) (cfg .emit xs [] work query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,transfer,goto,stepAux,cfg,store]

theorem finish_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .finish xs acc work query) (cfg .emit xs [] (acc.reverse++work) query) (acc.length+1) := by
  induction acc generalizing work with
  | nil => simpa using (finish_end (ea:=ea) (eb:=eb) (f:=f) xs work query)
  | cons b acc ih =>
    have he := (finish_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::work))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem initParse_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .initParse (true::b::xs) acc work query) (cfg .initParse xs acc (b::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,parse,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem initParse_end (xs acc work query : Bits) :
    Runs ea eb f (cfg .initParse (false::xs) acc work query) (cfg .initReverse xs acc work query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,parse,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem initParse_run (w xs acc work query : Bits) :
    Runs ea eb f (cfg .initParse (BitEncoding.frame w++xs) acc work query)
      (cfg .initReverse xs acc (w.reverse++work) query) (w.length+1) := by
  induction w generalizing work with
  | nil => simpa [BitEncoding.frame] using (initParse_end (ea:=ea) (eb:=eb) (f:=f) xs acc work query)
  | cons b w ih =>
    have he := (initParse_bit (ea:=ea) (eb:=eb) (f:=f) b (BitEncoding.frame w++xs) acc work query).trans (ih (b::work))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem parse_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .parse (true::b::xs) acc work query) (cfg .parse xs acc (b::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,parse,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem parse_end (xs acc work query : Bits) :
    Runs ea eb f (cfg .parse (false::xs) acc work query) (cfg .prepare xs acc work query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,parse,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem parse_run (w xs acc work query : Bits) :
    Runs ea eb f (cfg .parse (BitEncoding.frame w++xs) acc work query)
      (cfg .prepare xs acc (w.reverse++work) query) (w.length+1) := by
  induction w generalizing work with
  | nil => simpa [BitEncoding.frame] using (parse_end (ea:=ea) (eb:=eb) (f:=f) xs acc work query)
  | cons b w ih =>
    have he := (parse_bit (ea:=ea) (eb:=eb) (f:=f) b (BitEncoding.frame w++xs) acc work query).trans (ih (b::work))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem header_bit (b : Bool) (xs acc : Bits) :
    Runs ea eb f (cfg .header (true::b::xs) acc [] []) (cfg .header xs acc [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem header_end (xs acc : Bits) :
    Runs ea eb f (cfg .header (false::xs) acc [] []) (cfg .check xs acc [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem header_run (w xs acc : Bits) :
    Runs ea eb f (cfg .header (BitEncoding.frame w++xs) acc [] [])
      (cfg .check xs acc [] []) (w.length+1) := by
  induction w with
  | nil => exact header_end xs acc
  | cons b w ih =>
    simpa [BitEncoding.frame,Nat.add_comm] using
      (header_bit (ea:=ea) (eb:=eb) (f:=f) b (BitEncoding.frame w++xs) acc).trans ih

private theorem check_more (b : Bool) (xs acc : Bits) :
    Runs ea eb f (cfg .check (b::xs) acc [] []) (cfg .parse (b::xs) acc [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]

private theorem check_end (acc : Bits) :
    Runs ea eb f (cfg .check [] acc [] []) (cfg .finish [] acc [] []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]

private theorem check_frame (w xs acc : Bits) :
    Runs ea eb f (cfg .check (BitEncoding.frame w++xs) acc [] [])
      (cfg .parse (BitEncoding.frame w++xs) acc [] []) 1 := by
  cases w with
  | nil => exact check_more false xs acc
  | cons b w => exact check_more true (b::(BitEncoding.frame w++xs)) acc

private theorem frame_bit (b : Bool) (xs acc work query : Bits) :
    Runs ea eb f (cfg .frame xs (b::acc) work query) (cfg .frame xs acc (b::true::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem frame_end (xs work query : Bits) :
    Runs ea eb f (cfg .frame xs [] work query) (cfg .prefix xs [] (false::work) query) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

theorem frame_run (xs acc work query : Bits) :
    Runs ea eb f (cfg .frame xs acc work query)
      (cfg .prefix xs [] ((BitEncoding.frame acc).reverse++work) query) (acc.length+1) := by
  induction acc generalizing work with
  | nil => simpa [BitEncoding.frame] using (frame_end (ea:=ea) (eb:=eb) (f:=f) xs work query)
  | cons b acc ih =>
    have he := (frame_bit (ea:=ea) (eb:=eb) (f:=f) b xs acc work query).trans (ih (b::true::work))
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm] using he

private theorem emit_bit (b : Bool) (xs work : Bits) :
    Runs ea eb f (cfg .emit xs [] (b::work) []) (cfg .emit (b::xs) [] work []) 1 := by
  apply ordinary rfl
  simp [machine,FinTM2.step,step,program,goto,stepAux,cfg,store]
  funext k; cases k <;> rfl

private theorem emit_end (xs : Bits) :
    Runs ea eb f (cfg .emit xs [] [] []) (machine.final xs) 1 := by
  apply ordinary rfl
  apply congrArg some
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · funext k; cases k <;> simp [machine,program,stepAux,store,OracleTM2.final,haltList,Equiv.refl]

theorem emit_run (xs work : Bits) :
    Runs ea eb f (cfg .emit xs [] work []) (machine.final (work.reverse++xs)) (work.length+1) := by
  induction work generalizing xs with
  | nil => simpa using (emit_end (ea:=ea) (eb:=eb) (f:=f) xs)
  | cons b work ih =>
    have he := (emit_bit (ea:=ea) (eb:=eb) (f:=f) b xs work).trans (ih (b::xs))
    simpa [List.reverse_cons,List.append_assoc,Nat.add_comm] using he

theorem query_run (z : β) (a : α) (xs : Bits) :
    Runs ea eb f (cfg .query xs [] [] ((eb.prod ea).encode (z,a)))
      (cfg .answer xs [] [] (eb.encode (f z a)))
      (1+((eb.prod ea).encode (z,a)).length+(eb.encode (f z a)).length) := by
  have hq : machine.continuation (cfg .query xs [] [] ((eb.prod ea).encode (z,a)))=some .answer := rfl
  have hw : machine.queryWord (cfg .query xs [] [] ((eb.prod ea).encode (z,a)))=(eb.prod ea).encode (z,a) := by
    simp [machine,OracleTM2.queryWord,cfg,store,Equiv.refl]
  have he : machine.answerCfg (oracle ea eb f) (cfg .query xs [] [] ((eb.prod ea).encode (z,a))) .answer =
      cfg .answer xs [] [] (eb.encode (f z a)) := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,store,oracle]
      funext k; cases k <;> rfl
  refine ⟨1,_,[((eb.prod ea).encode (z,a),eb.encode (f z a))],?_,Nat.le_refl _,?_⟩
  · have h := OracleTM2.Run.query (m:=machine) (oracle:=oracle ea eb f) Label.answer hq
      (OracleTM2.Run.refl (machine.answerCfg (oracle ea eb f) (cfg .query xs [] [] ((eb.prod ea).encode (z,a))) .answer))
    rw [he] at h
    simpa only [hw,Nat.zero_add,oracle,ListMapMachines.typedOracle_encode] using h
  · intro qa ha
    exact ⟨(z,a),List.mem_singleton.mp ha⟩

def loopCost (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β) (z : β) : List α→ℕ
  | [] => 2*(eb.encode z).length+3
  | a::xs => 3*(ea.encode a).length+5*(eb.encode z).length+3*(eb.encode (f z a)).length+10 +
      loopCost ea eb f (f z a) xs

/-- The accumulator state and every actual query are tracked exactly. -/
theorem loop_run (z : β) (xs : List α) :
    Runs ea eb f (cfg .check (BitEncoding.frames (xs.map ea.encode)) (eb.encode z) [] [])
      (machine.final (eb.encode (xs.foldl f z))) (loopCost ea eb f z xs) := by
  induction xs generalizing z with
  | nil =>
    have h₁ := check_end (ea:=ea) (eb:=eb) (f:=f) (eb.encode z)
    have h₂ := finish_run (ea:=ea) (eb:=eb) (f:=f) [] (eb.encode z) [] []
    simp only [List.append_nil] at h₂
    have h₃ := emit_run (ea:=ea) (eb:=eb) (f:=f) [] (eb.encode z).reverse
    have h := (h₁.trans h₂).trans h₃
    have he : 1+((eb.encode z).length+1)+((eb.encode z).reverse.length+1) = 2*(eb.encode z).length+3 := by simp; omega
    rw [he] at h
    simpa [loopCost,BitEncoding.frames] using h
  | cons a xs ih =>
    let rest := BitEncoding.frames (xs.map ea.encode)
    have h₁ := check_frame (ea:=ea) (eb:=eb) (f:=f) (ea.encode a) rest (eb.encode z)
    have h₂ := parse_run (ea:=ea) (eb:=eb) (f:=f) (ea.encode a) rest (eb.encode z) [] []
    have h₃ := prepare_run (ea:=ea) (eb:=eb) (f:=f) rest (eb.encode z) (ea.encode a).reverse []
    have h₄ := frame_run (ea:=ea) (eb:=eb) (f:=f) rest (eb.encode z) [] (ea.encode a)
    have h₅ := prefix_run (ea:=ea) (eb:=eb) (f:=f) rest [] (BitEncoding.frame (eb.encode z)).reverse (ea.encode a)
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₂ h₃ h₄ h₅
    have h₆ := query_run (ea:=ea) (eb:=eb) (f:=f) z a rest
    have h₇ := answer_run (ea:=ea) (eb:=eb) (f:=f) rest [] [] (eb.encode (f z a))
    have h₈ := restore_run (ea:=ea) (eb:=eb) (f:=f) rest [] (eb.encode (f z a)).reverse []
    simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₇ h₈
    have h := (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans (ih (f z a))
    convert h using 1
    simp only [loopCost,BitEncoding.prod_length,BitEncoding.frame_length]
    ring

def foldTime (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β) (z : β) (xs : List α) : ℕ :=
  2*(eb.encode z).length+(BitEncoding.nat.encode xs.length).length+3+loopCost ea eb f z xs

theorem run (z : β) (xs : List α) :
    Runs ea eb f (machine.initial ((eb.prod ea.list).encode (z,xs)))
      (machine.final (eb.encode (xs.foldl f z))) (foldTime ea eb f z xs) := by
  have h₁ := initParse_run (ea:=ea) (eb:=eb) (f:=f) (eb.encode z) (ea.list.encode xs) [] [] []
  have h₂ := initReverse_run (ea:=ea) (eb:=eb) (f:=f) (ea.list.encode xs) [] (eb.encode z).reverse []
  simp only [List.append_nil,List.reverse_reverse,List.length_reverse] at h₁ h₂
  have h₃ := header_run (ea:=ea) (eb:=eb) (f:=f) (BitEncoding.nat.encode xs.length)
    (BitEncoding.frames (xs.map ea.encode)) (eb.encode z)
  have h₄ := loop_run (ea:=ea) (eb:=eb) (f:=f) z xs
  have h := ((h₁.trans h₂).trans h₃).trans h₄
  have hi : machine.initial ((eb.prod ea.list).encode (z,xs)) =
      cfg .initParse ((eb.prod ea.list).encode (z,xs)) [] [] [] := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · funext k; cases k <;> simp [machine,OracleTM2.initial,initList,cfg,store,Equiv.refl]
  rw [hi]
  convert h using 1
  · dsimp [foldTime]
    ring

theorem loopCost_bound (z : β) (xs : List α) (N P : ℕ)
    (hinput : ∀a∈xs,(ea.encode a).length≤N)
    (hacc : ∀i,i≤xs.length→(eb.encode ((xs.take i).foldl f z)).length≤P) :
    loopCost ea eb f z xs ≤ xs.length*(3*N+8*P+10)+2*P+3 := by
  induction xs generalizing z with
  | nil =>
    have hz := hacc 0 (by simp)
    simpa [loopCost] using Nat.add_le_add_right (Nat.mul_le_mul_left 2 hz) 3
  | cons a xs ih =>
    have hz := hacc 0 (by simp)
    have hfz := hacc 1 (by simp)
    have ha := hinput a (by simp)
    simp only [List.take_zero,List.foldl_nil,List.take_succ_cons,List.take_zero,List.foldl_cons,List.foldl_nil] at hz hfz
    have ht := ih (f z a) (fun b hb => hinput b (by simp [hb]))
      (fun i hi => by simpa only [List.take_succ_cons,List.foldl_cons] using hacc (i+1) (by simpa using hi))
    simp only [loopCost,List.length_cons]
    nlinarith

/-- All prefix accumulator encodings, rather than just the final result, must
satisfy the polynomial size invariant. -/
theorem foldTime_bound (p : Polynomial ℕ)
    (sizeBound : ∀z xs i,i≤xs.length→(eb.encode ((xs.take i).foldl f z)).length≤
      p.eval ((eb.prod ea.list).encode (z,xs)).length) (z : β) (xs : List α) :
    foldTime ea eb f z xs ≤
      ((Polynomial.C 10*Polynomial.X+Polynomial.C 10)*(Polynomial.X+p+Polynomial.C 4)).eval
        ((eb.prod ea.list).encode (z,xs)).length := by
  let N := ((eb.prod ea.list).encode (z,xs)).length
  let P := p.eval N
  have hpair : N=2*(eb.encode z).length+(ea.list.encode xs).length+1 := BitEncoding.prod_length _ _ _
  have hlist : (ea.list.encode xs).length = 2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun a => (ea.encode a).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hn : xs.length≤N := by omega
  have hinput (a : α) (ha : a∈xs) : (ea.encode a).length≤N := by
    have h := ListMapMachines.mem_le_sum_map (fun a => (ea.encode a).length) ha
    dsimp only at h
    omega
  have hl := loopCost_bound z xs N P hinput (sizeBound z xs)
  have hmul := Nat.mul_le_mul_right (3*N+8*P+10) hn
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,Polynomial.eval_X]
  change foldTime ea eb f z xs≤(10*N+10)*(N+P+4)
  change 2*(eb.encode z).length+(BitEncoding.nat.encode xs.length).length+3+loopCost ea eb f z xs ≤ (10*N+10)*(N+P+4)
  have hpre : 2*(eb.encode z).length+(BitEncoding.nat.encode xs.length).length ≤ N := by omega
  calc
    _ ≤ N+3+(N*(3*N+8*P+10)+2*P+3) := by omega
    _ ≤ _ := by nlinarith

/-- Actual bounded-fold compiler using canonical on-trace typed subroutine calls. -/
noncomputable def computer (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β)
    (body : TM2ComputableInPolyTime (eb.prod ea).toFinEncoding eb.toFinEncoding (fun p => f p.1 p.2))
    (p : Polynomial ℕ)
    (sizeBound : ∀z xs i,i≤xs.length→(eb.encode ((xs.take i).foldl f z)).length≤
      p.eval ((eb.prod ea.list).encode (z,xs)).length) :
    TM2ComputableInPolyTime (eb.prod ea.list).toFinEncoding eb.toFinEncoding
      (fun zx => zx.2.foldl f zx.1) := by
  let time : Polynomial ℕ := (Polynomial.C 10*Polynomial.X+Polynomial.C 10)*(Polynomial.X+p+Polynomial.C 4)
  let g := body.toTM2ComputableAux
  refine {
    tm := OracleSubstitution.machine machine g
    inputAlphabet := machine.core.inputAlphabet
    outputAlphabet := machine.core.outputAlphabet
    time := OracleSubstitution.timePolynomial machine time body.time
    outputsFun := ?_ }
  intro zx
  apply Classical.choice
  obtain ⟨steps,cost,qs,hr,hcost,hgood⟩ := run (ea:=ea) (eb:=eb) (f:=f) zx.1 zx.2
  have hN : ∀k,((machine.initial ((eb.prod ea.list).encode zx)).stk k).length≤
      ((eb.prod ea.list).encode zx).length := OracleReductionComposition.initial_length machine _
  have hc : cost≤time.eval ((eb.prod ea.list).encode zx).length :=
    hcost.trans (foldTime_bound p sizeBound zx.1 zx.2)
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
      ((eb.prod ea.list).encode zx).length cost hc)

theorem fp_foldl (ea : BitEncoding α) (eb : BitEncoding β) (f : β→α→β)
    (hf : FP (eb.prod ea) eb (fun p => f p.1 p.2)) (p : Polynomial ℕ)
    (sizeBound : ∀z xs i,i≤xs.length→(eb.encode ((xs.take i).foldl f z)).length≤
      p.eval ((eb.prod ea.list).encode (z,xs)).length) :
    FP (eb.prod ea.list) eb (fun zx => zx.2.foldl f zx.1) := by
  obtain ⟨body⟩ := hf
  exact ⟨computer ea eb f body p sizeBound⟩

end PlanarHom.ListFoldMachines
