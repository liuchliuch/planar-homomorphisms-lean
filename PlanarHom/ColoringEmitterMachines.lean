import PlanarHom.ColoringEmitterGrowth
import PlanarHom.RestrictedListFoldMachines

/-! NEW whole-emitter FP proof on every raw source input. The loop bound is on
the complete encoded state, including dictionary and all emitted occurrences. -/
namespace PlanarHom.ColoringEmitter
open Complexity PositiveBlockProgram PairProjectionMachines ArithmeticCircuitPrimitives
open ParsimoniousNorOneInThree

def seedEncoding : BitEncoding (ℕ × List Instruction) :=
  (stateEncoding.prod instructionEncoding.list).retract
    (fun p=>(initial p.1,p.2)) (fun p=>(p.1.sourceBase,p.2)) (by intro p; rfl)

theorem source_le_state_size (s : State) : s.sourceBase≤(stateEncoding.encode s).length := by
  simp only [stateEncoding,statePartsEncoding,BitEncoding.retract,BitEncoding.prod_length,
    BitEncoding.unaryNat_length]
  omega

theorem prefix_size (p : ℕ × List Instruction) (i : ℕ) (_hi : i≤p.2.length) :
    (stateEncoding.encode ((p.2.take i).foldl step (initial p.1))).length≤
      (Polynomial.C 10000000000*(Polynomial.X+1)^2).eval (seedEncoding.encode p).length := by
  let N:=(seedEncoding.encode p).length
  let ops:=p.2.take i
  let s:=ops.foldl step (initial p.1)
  let B:=3*p.1+5000*ops.length
  have he : N=2*(stateEncoding.encode (initial p.1)).length+
      (instructionEncoding.list.encode p.2).length+1 := by
    simp [N,seedEncoding,BitEncoding.retract,BitEncoding.prod_length]
  have hsrc:=source_le_state_size (initial p.1)
  change p.1≤(stateEncoding.encode (initial p.1)).length at hsrc
  have hn:p.1≤N := by omega
  have hlo:=instructionEncoding.list_length_le p.2
  have hk:ops.length≤N := by dsimp [ops]; simp only [List.length_take]; omega
  have hb:s.Bounded B := fold_bounded ops (initial p.1) (3*p.1) (initial_bounded p.1)
  have hl:=fold_lengths ops (initial p.1)
  change s.dictionary.length≤(initial p.1).dictionary.length+15*ops.length ∧
    s.edges.length≤(initial p.1).edges.length+3152*ops.length at hl
  simp only [initial,List.length_map,List.length_range,List.length_nil,Nat.zero_add] at hl
  have hdict:s.dictionary.length≤16*N := by omega
  have hedges:s.edges.length≤3152*N := by omega
  have hB:B+1≤5004*(N+1) := by dsimp [B]; omega
  have hlen:s.dictionary.length+s.edges.length+1≤3169*(N+1) := by omega
  have hp:=Nat.mul_le_mul hB hlen
  have hs:=state_code_bound s B hb
  change (stateEncoding.encode s).length≤(Polynomial.C 10000000000*(Polynomial.X+1)^2).eval N
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  nlinarith

theorem fp_run : FP seedEncoding stateEncoding (fun p=>run p.1 p.2) :=
  ⟨ListFoldMachines.computerOn seedEncoding instructionEncoding stateEncoding step
    (fun p=>initial p.1) Prod.snd (fun _=>rfl) (Classical.choice fp_step)
    (Polynomial.C 10000000000*(Polynomial.X+1)^2) prefix_size⟩

theorem fp_compile : FP formulaEncoding MixedCode.encoding compile := by
  have hn:=fp_fst BitEncoding.unaryNat clauseEncoding.list
  have hseed : FP formulaEncoding seedEncoding (fun f=>(f.1,PositiveRoutingCompiler.program f)) :=
    ((hn.comp fp_initial).pair PositiveBlockProgram.fp_program).transportOutput (fun _=>rfl)
  have hgraph:=(hseed.comp fp_run).comp fp_graphOf
  have hlen:=((fp_snd BitEncoding.unaryNat clauseEncoding.list).comp
    (ListUnaryLengthMachine.fp_length clauseEncoding)).comp UnaryNatConversionMachine.fp_conversion
  have ht:=(hlen.pair (fp_const formulaEncoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact (ht.ite (fp_const formulaEncoding MixedCode.encoding ⟨0,[],[]⟩) hgraph).congr
    (fun f=>by simp only [compile,Function.comp_apply,id_eq,List.length_eq_zero_iff])

theorem fp_unusedOriginal : FP formulaEncoding BitEncoding.unaryNat unusedOriginal := by
  have hn:=fp_fst BitEncoding.unaryNat clauseEncoding.list
  have hlen:=((fp_snd BitEncoding.unaryNat clauseEncoding.list).comp
    (ListUnaryLengthMachine.fp_length clauseEncoding)).comp UnaryNatConversionMachine.fp_conversion
  have ht:=(hlen.pair (fp_const formulaEncoding BitEncoding.nat 0)).comp NatListSumMachines.fp_equal
  exact (ht.ite hn (fp_const formulaEncoding BitEncoding.unaryNat 0)).congr
    (fun f=>by simp only [unusedOriginal,Function.comp_apply,id_eq,List.length_eq_zero_iff])

end PlanarHom.ColoringEmitter
