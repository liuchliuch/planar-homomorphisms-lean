import PlanarHom.MixedParallelLoops

namespace PlanarHom.MixedParallelMachines
open Turing Turing.TM2 PlanarHom.Complexity

private theorem halt_run (selected : ℕ) (out : Bits) :
    Runs selected (cfg .halt false {output:=out}) (machine.final out) 1 := by
  apply ordinary selected rfl
  simp [machine,OracleTM2.final,FinTM2.step,step,program,stepAux,cfg,haltList,Equiv.refl]
  funext k; cases k <;> rfl

/-- The new binary edge list is re-escaped as the first component of the mixed
occurrence pair. The complete original unary-list codeword is restored verbatim. -/
theorem finalize_run (selected : ℕ) (F V P U : Bits) (k : ℕ) :
    Runs selected
      (cfg .reversePayload false {factor:=F,vertices:=(BitEncoding.frame V).reverse,payload:=P.reverse,count:=BitEncoding.nat.encode k,unaries:=U.reverse})
      (machine.final (BitEncoding.frame V++BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)++U))
      (4*P.length+9*k+U.length+2*V.length+F.length+15) := by
  have h₁ := transfer selected false .payload .output (by decide) .reversePayload .frameCount rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,payload:=P.reverse,count:=BitEncoding.nat.encode k,unaries:=U.reverse}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₁
  have h₂ := count_run selected false {factor:=F,vertices:=(BitEncoding.frame V).reverse,output:=P,unaries:=U.reverse}
    (BitEncoding.nat.encode k)
  simp only [List.append_nil] at h₂
  have h₃ := transfer selected false .buffer .output (by decide) .prefixCount .frameEdges rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame (BitEncoding.nat.encode k)).reverse,output:=P,unaries:=U.reverse}
  simp only [Data.get,Data.set,List.length_reverse,List.reverse_reverse] at h₃
  have h₄ := frame_edges_run selected false {factor:=F,vertices:=(BitEncoding.frame V).reverse,unaries:=U.reverse}
    (BitEncoding.frame (BitEncoding.nat.encode k)++P)
  simp only [List.append_nil] at h₄
  have h₅ := transfer selected false .unaries .output (by decide) .restoreUnaries .prefixEdges rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)).reverse,unaries:=U.reverse}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₅
  have h₆ := transfer selected false .buffer .output (by decide) .prefixEdges .prefixVertices rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)).reverse,output:=U}
  simp only [Data.get,Data.set,List.length_reverse,List.reverse_reverse] at h₆
  have h₇ := transfer selected false .vertices .output (by decide) .prefixVertices .clearFactor rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,output:=BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)++U}
  simp only [Data.get,Data.set,List.length_reverse,List.reverse_reverse] at h₇
  have h₈ := clear selected false .factor .clearFactor .halt rfl rfl
    {factor:=F,output:=BitEncoding.frame V++(BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)++U)}
  simp only [Data.get,Data.set] at h₈
  have h₉ := halt_run selected (BitEncoding.frame V++(BitEncoding.frame (BitEncoding.frame (BitEncoding.nat.encode k)++P)++U))
  have h := (((((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆).trans h₇).trans h₈).trans h₉
  rw [List.append_assoc]
  apply h.mono
  have hk := encodeNat_length_le k
  simp only [BitEncoding.frame_length,List.length_append]
  omega

theorem initial_eq (word : Bits) : machine.initial word=cfg .factor false {input:=word} := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp [machine,OracleTM2.initial,initList,cfg,Equiv.refl]
    funext k; cases k <;> rfl

/-- Parse and preserve all enclosing mixed-code framing, saving the untouched
unary suffix before scanning any binary edge occurrence. -/
theorem prefix_run (selected : ℕ) (F V H P U : Bits) :
    Runs selected (machine.initial (BitEncoding.frame F++BitEncoding.frame V++BitEncoding.frame (BitEncoding.frame H++P)++U))
      (cfg .startEdge false {input:=P,factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse,unaries:=U.reverse})
      (F.length+V.length+2*(BitEncoding.frame H++P).length+U.length+H.length+6) := by
  have h₁ := factor_run selected false {} F (BitEncoding.frame V++BitEncoding.frame (BitEncoding.frame H++P)++U)
  simp only [List.append_nil,List.append_assoc] at h₁
  have h₂ := vertices_run selected false {factor:=F.reverse} V (BitEncoding.frame (BitEncoding.frame H++P)++U)
  simp only [List.append_nil] at h₂
  have h₃ := outer_run selected false {factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse} (BitEncoding.frame H++P) U
  simp only [List.append_nil] at h₃
  have h₄ := transfer selected false .input .unaries (by decide) .saveUnaries .restoreEdges rfl rfl
    {input:=U,factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame H++P).reverse}
  simp only [Data.get,Data.set,List.append_nil] at h₄
  have h₅ := transfer selected false .buffer .input (by decide) .restoreEdges .header rfl rfl
    {factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame H++P).reverse,unaries:=U.reverse}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₅
  have h₆ := header_run selected false {factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse,unaries:=U.reverse} H P
  have h := ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆
  rw [initial_eq]
  convert h using 1
  · simp only [List.append_assoc]
  · omega

end PlanarHom.MixedParallelMachines
