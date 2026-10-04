import PlanarHom.GraphParallelMachineCore

namespace PlanarHom.GraphParallelMachines
open Turing Turing.TM2 PlanarHom.Complexity PlanarHom.BinaryArithmetic

private theorem step_run (l next : Label) (hn : machine.request l = none) (d d' : Data)
    (hs : stepAux (program l) ((),none) d.get = cfg next d') :
    Runs (cfg l d) (cfg next d') 1 := ordinary hn (congrArg some hs)

private theorem factor_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .factor {d with input:=true::b::tail})
      (cfg .factor {d with input:=tail,factor:=b::d.factor}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem factor_nil (d : Data) (tail : Bits) :
    Runs (cfg .factor {d with input:=false::tail}) (cfg .vertices {d with input:=tail}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem vertices_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .vertices {d with input:=true::b::tail})
      (cfg .vertices {d with input:=tail,vertices:=b::true::d.vertices}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem vertices_nil (d : Data) (tail : Bits) :
    Runs (cfg .vertices {d with input:=false::tail})
      (cfg .header {d with input:=tail,vertices:=false::d.vertices}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem header_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .header {d with input:=true::b::tail}) (cfg .header {d with input:=tail}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem header_nil (d : Data) (tail : Bits) :
    Runs (cfg .header {d with input:=false::tail}) (cfg .edge {d with input:=tail}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem edge_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .edge {d with input:=true::b::tail})
      (cfg .edge {d with input:=tail,buffer:=b::true::d.buffer}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem edge_nil (d : Data) (tail : Bits) :
    Runs (cfg .edge {d with input:=false::tail})
      (cfg .reverseEdge {d with input:=tail,buffer:=false::d.buffer}) 1 := by
  apply step_run _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

theorem edge_eof (d : Data) :
    Runs (cfg .edge {d with input:=[]}) (cfg .reversePayload {d with input:=[]}) 1 := by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]

private theorem count_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .frameCount {d with count:=b::tail})
      (cfg .frameCount {d with count:=tail,buffer:=b::true::d.buffer}) 1 := by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

private theorem count_nil (d : Data) :
    Runs (cfg .frameCount {d with count:=[]})
      (cfg .prefixCount {d with count:=[],buffer:=false::d.buffer}) 1 := by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

theorem check_cons (d : Data) (b : Bool) (tail : Bits) :
    Runs (cfg .check {d with factor:=b::tail})
      (cfg .emit {d with factor:=tail,back:=b::d.back}) 1 := by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

theorem check_nil (d : Data) :
    Runs (cfg .check {d with factor:=[]}) (cfg .restoreFactor {d with factor:=[]}) 1 := by
  apply step_run _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  funext k; cases k <;> rfl

/-- Parse the unary multiplier one explicitly materialized bit per transition. -/
theorem factor_run (d : Data) (word tail : Bits) :
    Runs (cfg .factor {d with input:=BitEncoding.frame word++tail})
      (cfg .vertices {d with input:=tail,factor:=word.reverse++d.factor}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using factor_nil d tail
  | cons b bs ih =>
    have h := (factor_cons d b (BitEncoding.frame bs++tail)).trans (ih {d with factor:=b::d.factor})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem vertices_run (d : Data) (word tail : Bits) :
    Runs (cfg .vertices {d with input:=BitEncoding.frame word++tail})
      (cfg .header {d with input:=tail,vertices:=(BitEncoding.frame word).reverse++d.vertices})
      (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using vertices_nil d tail
  | cons b bs ih =>
    have h := (vertices_cons d b (BitEncoding.frame bs++tail)).trans
      (ih {d with vertices:=b::true::d.vertices})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem header_run (d : Data) (word tail : Bits) :
    Runs (cfg .header {d with input:=BitEncoding.frame word++tail})
      (cfg .edge {d with input:=tail}) (word.length+1) := by
  induction word with
  | nil => simpa [BitEncoding.frame] using header_nil d tail
  | cons b bs ih =>
    have h := (header_cons d b (BitEncoding.frame bs++tail)).trans ih
    simpa [BitEncoding.frame,Nat.add_comm,Nat.add_left_comm] using h

theorem edge_run (d : Data) (word tail : Bits) :
    Runs (cfg .edge {d with input:=BitEncoding.frame word++tail})
      (cfg .reverseEdge {d with input:=tail,buffer:=(BitEncoding.frame word).reverse++d.buffer})
      (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using edge_nil d tail
  | cons b bs ih =>
    have h := (edge_cons d b (BitEncoding.frame bs++tail)).trans
      (ih {d with buffer:=b::true::d.buffer})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem count_run (d : Data) (word : Bits) :
    Runs (cfg .frameCount {d with count:=word})
      (cfg .prefixCount {d with count:=[],buffer:=(BitEncoding.frame word).reverse++d.buffer})
      (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using count_nil d
  | cons b bs ih =>
    have h := (count_cons d b bs).trans (ih {d with buffer:=b::true::d.buffer})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem query_run (d : Data) :
    Runs (cfg .query d) (cfg .check {d with count:=succBits d.count})
      (1+d.count.length+(succBits d.count).length) := by
  have hq : machine.continuation (cfg .query d) = some .check := rfl
  have hw : machine.queryWord (cfg .query d) = d.count := by
    simp [machine,OracleTM2.queryWord,cfg,Data.get,Equiv.refl]
  have he : machine.answerCfg succBits (cfg .query d) .check =
      cfg .check {d with count:=succBits d.count} := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,Data.get]
      funext k; cases k <;> rfl
  refine ⟨1,_,[(d.count,succBits d.count)],?_,Nat.le_refl _⟩
  have h := OracleTM2.Run.query (m:=machine) (oracle:=succBits) Label.check hq (OracleTM2.Run.refl (machine.answerCfg succBits (cfg .query d) .check))
  simpa only [he,hw,Nat.zero_add] using h

theorem query_count (d : Data) (n : ℕ) :
    Runs (cfg .query {d with count:=BitEncoding.nat.encode n})
      (cfg .check {d with count:=BitEncoding.nat.encode (n+1)}) (2*n+2) := by
  have h := query_run {d with count:=BitEncoding.nat.encode n}
  rw [show succBits (BitEncoding.nat.encode n) = BitEncoding.nat.encode (n+1)
    from succBits_encodeNat n] at h
  dsimp only at h
  apply h.mono
  have hn := encodeNat_length_le n
  have hn' := encodeNat_length_le (n+1)
  omega

end PlanarHom.GraphParallelMachines
