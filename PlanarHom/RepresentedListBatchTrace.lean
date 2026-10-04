import PlanarHom.ListMapMachines
import PlanarHom.RepresentedBitModel

/-! Exact transcript strengthening of the existing actual list-map machine.
The machine/program are reused literally. Every listed query is made once,
in order, and arbitrary answer words are retained and charged. -/
namespace PlanarHom.RepresentedListBatch
open Turing Turing.TM2 Complexity MachineComposition
open ListMapMachines (Stack Label State Statement store goto program machine cfg
  typedOracle typedOracle_encode Good itemCost mapCost mapTime)

def Runs {α β : Type} (ea : BitEncoding α) (eb : BitEncoding β) (f : α→β)
    (c d : machine.Cfg) (bound : ℕ) (requests : List α := []) : Prop :=
  ∃s t qs,machine.Run (typedOracle ea eb f) c d s t qs ∧ t≤bound ∧
    (∀qa∈qs,Good ea eb f qa) ∧ qs=requests.map (fun a=>(ea.encode a,eb.encode (f a)))

variable {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β} {f : α→β}

theorem Runs.trans {c d z : machine.Cfg} {n k : ℕ} {rs ss:List α}
    (h : Runs ea eb f c d n rs) (h' : Runs ea eb f d z k ss) : Runs ea eb f c z (n+k) (rs++ss) := by
  obtain ⟨s,t,qs,hr,ht,hgood,heq⟩ := h
  obtain ⟨s',t',qs',hr',ht',hgood',heq'⟩ := h'
  refine ⟨_,_,_,hr.trans hr',Nat.add_le_add ht ht',?_,?_⟩
  · intro qa ha
    rcases List.mem_append.mp ha with ha|ha
    · exact hgood qa ha
    · exact hgood' qa ha
  · simp only [heq,heq',List.map_append]

theorem Runs.mono {c d : machine.Cfg} {n k : ℕ} {rs:List α}
    (h : Runs ea eb f c d n rs) (hk : n≤k) : Runs ea eb f c d k rs := by
  obtain ⟨s,t,qs,hr,ht,hgood,heq⟩ := h
  exact ⟨s,t,qs,hr,ht.trans hk,hgood,heq⟩

theorem ordinary {c d : machine.Cfg} (hn : machine.continuation c=none)
    (hs : machine.core.tm.step c=some d) : Runs ea eb f c d 1 :=
  ⟨1,1,[],.ordinary hn hs (.refl d),by rfl,by simp,rfl⟩

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
      (1+(ea.encode a).length+(eb.encode (f a)).length) [a] := by
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
  refine ⟨1,_,[(ea.encode a,eb.encode (f a))],?_,Nat.le_refl _,?_,rfl⟩
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

/-- Every oracle call in the complete loop is exactly an encoded list element. -/
theorem loop_run (xs : List α) (out : Bits) :
    Runs ea eb f (cfg .check (BitEncoding.frames (xs.map ea.encode)) out [] [])
      (cfg .finish [] ((BitEncoding.frames ((xs.map f).map eb.encode)).reverse++out) [] [])
      (mapCost ea eb f xs+1) xs := by
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
    simp only [List.nil_append,List.append_nil] at h
    convert h using 1
    · simp [BitEncoding.frames,List.reverse_append,List.append_assoc]
    · simp [mapCost,itemCost]
      ring

/-- The original canonical length header is preserved verbatim; every mapped
item is separately framed and all four caller stacks are cleared at halt. -/
theorem run (xs : List α) :
    Runs ea eb f (machine.initial (ea.list.encode xs)) (machine.final (eb.list.encode (xs.map f)))
      (mapTime ea eb f xs) xs := by
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
  simp only [List.nil_append,List.append_nil] at h
  convert h using 1
  · simp [BitEncoding.list,output,header,List.reverse_append]
  · simp only [mapTime,header,output,List.length_append,List.length_reverse,
      BitEncoding.list,List.length_map]
    omega

end PlanarHom.RepresentedListBatch
