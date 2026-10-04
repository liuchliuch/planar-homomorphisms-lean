import PlanarHom.GraphParallelLoops

namespace PlanarHom.GraphParallelMachines
open Turing Turing.TM2 PlanarHom.Complexity

private theorem halt_run (out : Bits) : Runs (cfg .halt {output:=out}) (machine.final out) 1 := by
  apply ordinary rfl
  simp [machine,OracleTM2.final,FinTM2.step,step,program,stepAux,cfg,haltList,Equiv.refl]
  funext k; cases k <;> rfl

/-- Materialize the new count framing and restore the saved vertex prefix, then
clear the multiplier. The final configuration has no auxiliary garbage. -/
theorem finalize_run (F V P : Bits) (k : ℕ) :
    Runs (cfg .reversePayload {factor:=F,vertices:=(BitEncoding.frame V).reverse,payload:=P.reverse,count:=BitEncoding.nat.encode k})
      (machine.final (BitEncoding.frame V++BitEncoding.frame (BitEncoding.nat.encode k)++P))
      (P.length+3*k+2*V.length+F.length+8) := by
  have h₁ := transfer .payload .output (by decide) .reversePayload .frameCount rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,payload:=P.reverse,count:=BitEncoding.nat.encode k}
  simp only [Data.get,Data.set,List.append_nil,List.length_reverse,List.reverse_reverse] at h₁
  have h₂ := count_run {factor:=F,vertices:=(BitEncoding.frame V).reverse,output:=P} (BitEncoding.nat.encode k)
  simp only [List.append_nil] at h₂
  have h₃ := transfer .buffer .output (by decide) .prefixCount .prefixVertices rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,buffer:=(BitEncoding.frame (BitEncoding.nat.encode k)).reverse,output:=P}
  simp only [Data.get,Data.set,List.length_reverse,List.reverse_reverse] at h₃
  have h₄ := transfer .vertices .output (by decide) .prefixVertices .clearFactor rfl rfl
    {factor:=F,vertices:=(BitEncoding.frame V).reverse,output:=BitEncoding.frame (BitEncoding.nat.encode k)++P}
  simp only [Data.get,Data.set,List.length_reverse,List.reverse_reverse] at h₄
  have h₅ := clear .factor .clearFactor .halt rfl rfl
    {factor:=F,output:=BitEncoding.frame V++(BitEncoding.frame (BitEncoding.nat.encode k)++P)}
  simp only [Data.get,Data.set] at h₅
  have h₆ := halt_run (BitEncoding.frame V++(BitEncoding.frame (BitEncoding.nat.encode k)++P))
  have h := ((((h₁.trans h₂).trans h₃).trans h₄).trans h₅).trans h₆
  rw [List.append_assoc]
  apply h.mono
  have hk := encodeNat_length_le k
  simp only [BitEncoding.frame_length]
  omega

theorem initial_eq (word : Bits) : machine.initial word = cfg .factor {input:=word} := by
  apply OracleSubstitution.cfg_ext
  · rfl
  · rfl
  · simp [machine,OracleTM2.initial,initList,cfg,Equiv.refl]
    funext k; cases k <;> rfl

/-- The three original headers are processed by actual finite parsers. Only the
obsolete occurrence count is discarded; the vertex prefix is saved exactly. -/
theorem prefix_run (F V H P : Bits) :
    Runs (machine.initial (BitEncoding.frame F++BitEncoding.frame V++BitEncoding.frame H++P))
      (cfg .edge {input:=P,factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse})
      (F.length+V.length+H.length+3) := by
  have h₁ := factor_run {} F (BitEncoding.frame V++BitEncoding.frame H++P)
  simp only [List.append_nil,List.append_assoc] at h₁
  have h₂ := vertices_run {factor:=F.reverse} V (BitEncoding.frame H++P)
  simp only [List.append_nil] at h₂
  have h₃ := header_run {factor:=F.reverse,vertices:=(BitEncoding.frame V).reverse} H P
  have h := (h₁.trans h₂).trans h₃
  rw [initial_eq]
  simpa only [List.append_assoc,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h

end PlanarHom.GraphParallelMachines
