import PlanarHom.MixedParallelMachineCore

namespace PlanarHom.MixedParallelMachines
open Turing Turing.TM2 PlanarHom.Complexity

private theorem step_run (selected : ℕ) (l next : Label) (hn : machine.request l=none)
    (flag flag' : Bool) (d d' : Data)
    (hs : stepAux (program l) (flag,none) d.get=cfg next flag' d') :
    Runs selected (cfg l flag d) (cfg next flag' d') 1 := ordinary selected hn (congrArg some hs)

theorem factor_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .factor flag {d with input:=true::b::tail}) (cfg .factor flag {d with input:=tail,factor:=b::d.factor}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem factor_nil (selected : ℕ) (flag : Bool) (d : Data) (tail : Bits) :
    Runs selected (cfg .factor flag {d with input:=false::tail}) (cfg .vertices flag {d with input:=tail}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem vertices_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .vertices flag {d with input:=true::b::tail}) (cfg .vertices flag {d with input:=tail,vertices:=b::true::d.vertices}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem vertices_nil (selected : ℕ) (flag : Bool) (d : Data) (tail : Bits) :
    Runs selected (cfg .vertices flag {d with input:=false::tail}) (cfg .outerEdges flag {d with input:=tail,vertices:=false::d.vertices}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem outer_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .outerEdges flag {d with input:=true::b::tail}) (cfg .outerEdges flag {d with input:=tail,buffer:=b::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem outer_nil (selected : ℕ) (flag : Bool) (d : Data) (tail : Bits) :
    Runs selected (cfg .outerEdges flag {d with input:=false::tail}) (cfg .saveUnaries flag {d with input:=tail}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem header_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .header flag {d with input:=true::b::tail}) (cfg .header flag {d with input:=tail}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem header_nil (selected : ℕ) (flag : Bool) (d : Data) (tail : Bits) :
    Runs selected (cfg .header flag {d with input:=false::tail}) (cfg .startEdge flag {d with input:=tail}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,parseStmt,pushParsed,endParsed,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem edge_start (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .startEdge flag {d with input:=b::tail}) (cfg .saveCounter flag {d with input:=b::tail}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]


theorem edge_eof (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .startEdge flag {d with input:=[]}) (cfg .reversePayload flag {d with input:=[]}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]


theorem edge_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .edge flag {d with input:=true::b::tail}) (cfg .edge flag {d with input:=tail,buffer:=b::true::d.buffer,classifier:=b::d.classifier}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem edge_nil (selected : ℕ) (flag : Bool) (d : Data) (tail : Bits) :
    Runs selected (cfg .edge flag {d with input:=false::tail}) (cfg .reverseEdge flag {d with input:=tail,buffer:=false::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem tag_class (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .tagClass flag d) (cfg .queryClass flag {d with count:=true::d.count}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem read_class (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) :
    Runs selected (cfg .readClass flag {d with count:=[b]}) (cfg .restoreCounter b {d with count:=[]}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem route_true (selected : ℕ) (d : Data)  :
    Runs selected (cfg .route true d) (cfg .check true d) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg]


theorem route_false (selected : ℕ) (d : Data)  :
    Runs selected (cfg .route false d) (cfg .emit false d) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg]


theorem check_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .check flag {d with factor:=b::tail}) (cfg .emit flag {d with factor:=tail,back:=b::d.back}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem check_nil (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .check flag {d with factor:=[]}) (cfg .restoreFactor flag {d with factor:=[]}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem tag_inc_true (selected : ℕ) (d : Data)  :
    Runs selected (cfg .tagInc true d) (cfg .queryRepeat true {d with count:=false::d.count}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem tag_inc_false (selected : ℕ) (d : Data)  :
    Runs selected (cfg .tagInc false d) (cfg .querySingle false {d with count:=false::d.count}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem next_edge (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .nextEdge flag d) (cfg .startEdge false d) 1 := by
  apply step_run selected _ _ rfl
  simp [program,stepAux,cfg]


theorem count_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .frameCount flag {d with count:=b::tail}) (cfg .frameCount flag {d with count:=tail,buffer:=b::true::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,frameStmt,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem count_nil (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .frameCount flag {d with count:=[]}) (cfg .prefixCount flag {d with count:=[],buffer:=false::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,frameStmt,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem frame_edges_cons (selected : ℕ) (flag : Bool) (d : Data) (b : Bool) (tail : Bits) :
    Runs selected (cfg .frameEdges flag {d with output:=b::tail}) (cfg .frameEdges flag {d with output:=tail,buffer:=b::true::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,frameStmt,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem frame_edges_nil (selected : ℕ) (flag : Bool) (d : Data)  :
    Runs selected (cfg .frameEdges flag {d with output:=[]}) (cfg .restoreUnaries flag {d with output:=[],buffer:=false::d.buffer}) 1 := by
  apply step_run selected _ _ rfl
  simp [program,resetGoto,frameStmt,stepAux,cfg,Data.get]
  try (funext k; cases k <;> rfl)

theorem factor_run (selected : ℕ) (flag : Bool) (d : Data) (word tail : Bits) :
    Runs selected (cfg .factor flag {d with input:=BitEncoding.frame word++tail})
      (cfg .vertices flag {d with input:=tail,factor:=word.reverse++d.factor}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using factor_nil selected flag d tail
  | cons b bs ih =>
    have h := (factor_cons selected flag d b (BitEncoding.frame bs++tail)).trans (ih {d with factor:=b::d.factor})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem vertices_run (selected : ℕ) (flag : Bool) (d : Data) (word tail : Bits) :
    Runs selected (cfg .vertices flag {d with input:=BitEncoding.frame word++tail})
      (cfg .outerEdges flag {d with input:=tail,vertices:=(BitEncoding.frame word).reverse++d.vertices}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using vertices_nil selected flag d tail
  | cons b bs ih =>
    have h := (vertices_cons selected flag d b (BitEncoding.frame bs++tail)).trans (ih {d with vertices:=b::true::d.vertices})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem outer_run (selected : ℕ) (flag : Bool) (d : Data) (word tail : Bits) :
    Runs selected (cfg .outerEdges flag {d with input:=BitEncoding.frame word++tail})
      (cfg .saveUnaries flag {d with input:=tail,buffer:=word.reverse++d.buffer}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using outer_nil selected flag d tail
  | cons b bs ih =>
    have h := (outer_cons selected flag d b (BitEncoding.frame bs++tail)).trans (ih {d with buffer:=b::d.buffer})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem header_run (selected : ℕ) (flag : Bool) (d : Data) (word tail : Bits) :
    Runs selected (cfg .header flag {d with input:=BitEncoding.frame word++tail})
      (cfg .startEdge flag {d with input:=tail}) (word.length+1) := by
  induction word with
  | nil => simpa [BitEncoding.frame] using header_nil selected flag d tail
  | cons b bs ih =>
    have h := (header_cons selected flag d b (BitEncoding.frame bs++tail)).trans ih
    simpa [BitEncoding.frame,Nat.add_comm,Nat.add_left_comm] using h

theorem edge_run (selected : ℕ) (flag : Bool) (d : Data) (word tail : Bits) :
    Runs selected (cfg .edge flag {d with input:=BitEncoding.frame word++tail})
      (cfg .reverseEdge flag {d with input:=tail,buffer:=(BitEncoding.frame word).reverse++d.buffer,classifier:=word.reverse++d.classifier})
      (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using edge_nil selected flag d tail
  | cons b bs ih =>
    have h := (edge_cons selected flag d b (BitEncoding.frame bs++tail)).trans
      (ih {d with buffer:=b::true::d.buffer,classifier:=b::d.classifier})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem count_run (selected : ℕ) (flag : Bool) (d : Data) (word : Bits) :
    Runs selected (cfg .frameCount flag {d with count:=word})
      (cfg .prefixCount flag {d with count:=[],buffer:=(BitEncoding.frame word).reverse++d.buffer}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using count_nil selected flag d
  | cons b bs ih =>
    have h := (count_cons selected flag d b bs).trans (ih {d with buffer:=b::true::d.buffer})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem frame_edges_run (selected : ℕ) (flag : Bool) (d : Data) (word : Bits) :
    Runs selected (cfg .frameEdges flag {d with output:=word})
      (cfg .restoreUnaries flag {d with output:=[],buffer:=(BitEncoding.frame word).reverse++d.buffer}) (word.length+1) := by
  induction word generalizing d with
  | nil => simpa [BitEncoding.frame] using frame_edges_nil selected flag d
  | cons b bs ih =>
    have h := (frame_edges_cons selected flag d b bs).trans (ih {d with buffer:=b::true::d.buffer})
    simpa [BitEncoding.frame,List.reverse_cons,List.append_assoc,Nat.add_comm,Nat.add_left_comm] using h

theorem oracle_run (selected : ℕ) (flag : Bool) (l next : Label) (hq : machine.request l=some next) (d : Data) :
    Runs selected (cfg l flag d) (cfg next flag {d with count:=selectedOracle selected d.count})
      (1+d.count.length+(selectedOracle selected d.count).length) := by
  have hqc : machine.continuation (cfg l flag d)=some next := hq
  have hw : machine.queryWord (cfg l flag d)=d.count := by simp [machine,OracleTM2.queryWord,cfg,Data.get,Equiv.refl]
  have he : machine.answerCfg (selectedOracle selected) (cfg l flag d) next=
      cfg next flag {d with count:=selectedOracle selected d.count} := by
    apply OracleSubstitution.cfg_ext
    · rfl
    · rfl
    · simp [OracleTM2.answerCfg,machine,OracleTM2.queryWord,cfg,Equiv.refl,Data.get]
      funext k; cases k <;> rfl
  refine ⟨1,_,[(d.count,selectedOracle selected d.count)],?_,Nat.le_refl _⟩
  have h := OracleTM2.Run.query (m:=machine) (oracle:=selectedOracle selected) next hqc
    (OracleTM2.Run.refl (machine.answerCfg (selectedOracle selected) (cfg l flag d) next))
  simpa only [he,hw,Nat.zero_add] using h

theorem classify_query (selected : ℕ) (flag : Bool) (d : Data) (word : Bits) :
    Runs selected (cfg .queryClass flag {d with count:=true::word})
      (cfg .readClass flag {d with count:=[labelMatches selected word]}) (word.length+3) := by
  simpa [selectedOracle,Nat.add_comm,Nat.add_left_comm] using
    oracle_run selected flag .queryClass .readClass rfl {d with count:=true::word}

theorem increment_query (selected : ℕ) (flag : Bool) (l next : Label) (hq : machine.request l=some next)
    (d : Data) (n : ℕ) :
    Runs selected (cfg l flag {d with count:=false::BitEncoding.nat.encode n})
      (cfg next flag {d with count:=BitEncoding.nat.encode (n+1)}) (2*n+3) := by
  have h := oracle_run selected flag l next hq {d with count:=false::BitEncoding.nat.encode n}
  simp only [selectedOracle_succ,List.length_cons] at h
  apply h.mono
  have hn := encodeNat_length_le n
  have hn' := encodeNat_length_le (n+1)
  omega

end PlanarHom.MixedParallelMachines
