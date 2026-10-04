import PlanarHom.RoutingFoldGrowth
import PlanarHom.RestrictedListFoldMachines

/-! Actual polynomial-time routing fold, with explicit bounds on all reachable
serialized accumulators. The initial unary range is part of the input word. -/
namespace PlanarHom.PositiveBlockProgram
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ParsimoniousNorOneInThree

private theorem list_code_bound {A : Type} (e : BitEncoding A) (xs : List A) (B : ℕ)
    (h : ∀x∈xs,(e.encode x).length≤B) : (e.list.encode xs).length≤(2*B+3)*xs.length+1 := by
  have hn := Complexity.encodeNat_length_le xs.length
  have hs := List.sum_le_card_nsmul (xs.map (fun x => (e.encode x).length)) B (by
    intro v hv
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
    exact h x hx)
  simp only [List.length_map,smul_eq_mul] at hs
  have he : (e.list.encode xs).length=2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun x => (e.encode x).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  rw [he]
  change (BitEncoding.nat.encode xs.length).length≤xs.length at hn
  nlinarith

private theorem instruction_code_bound (B : ℕ) (op : Instruction) (h : op.Bounded B) :
    (instructionEncoding.encode op).length≤5*B+11 := by
  have h1 := (Complexity.encodeNat_length_le op.2.1).trans h.1
  have h2 := (Complexity.encodeNat_length_le op.2.2.1).trans h.2.1
  have h3 := (Complexity.encodeNat_length_le op.2.2.2).trans h.2.2
  have hk : (kindEncoding.encode op.1).length=4 := by cases op.1 <;> rfl
  simp only [instructionEncoding,referenceEncoding,BitEncoding.prod_length,hk]
  omega

theorem layer_code_bound (r : LayerResult) (h : r.Bounded) :
    (layerEncoding.encode r).length≤100*(r.variableCount+1)*(r.rails.length+r.instructions.length+1) := by
  have hr := list_code_bound BitEncoding.nat r.rails r.variableCount
    (fun x hx => (Complexity.encodeNat_length_le x).trans (h.1 x hx))
  have hc := list_code_bound instructionEncoding r.instructions (5*r.variableCount+11)
    (fun op hop => instruction_code_bound _ op (h.2 op hop))
  have he : (layerEncoding.encode r).length=2*r.variableCount+2*(BitEncoding.nat.list.encode r.rails).length+
      (instructionEncoding.list.encode r.instructions).length+2 := by
    simp [layerEncoding,layerPartsEncoding,BitEncoding.retract,BitEncoding.prod_length]
    omega
  rw [he]
  nlinarith

def routingSeedEncoding : BitEncoding (ℕ × List Stage) :=
  (layerEncoding.prod stageEncoding.list).retract
    (fun p => (LayerResult.identity p.1 (List.range p.1),p.2))
    (fun p => (p.1.variableCount,p.2)) (by intro p; rfl)

theorem initial_bounded (n : ℕ) : (LayerResult.identity n (List.range n)).Bounded := by
  constructor
  · intro x hx
    exact (List.mem_range.mp hx).le
  · simp [LayerResult.identity]

/-- This bound covers every prefix, including noncanonical and invalid stages. -/
theorem routing_prefix_size (p : ℕ × List Stage) (i : ℕ) (_hi : i≤p.2.length) :
    (layerEncoding.encode ((p.2.take i).foldl advance (.identity p.1 (List.range p.1)))).length≤
      (Polynomial.C 100000*(Polynomial.X+1)^4).eval (routingSeedEncoding.encode p).length := by
  let N := (routingSeedEncoding.encode p).length
  let r := (p.2.take i).foldl advance (.identity p.1 (List.range p.1))
  have he : N=2*(2*p.1+2*(BitEncoding.nat.list.encode (List.range p.1)).length+
      (instructionEncoding.list.encode []).length+2)+(stageEncoding.list.encode p.2).length+1 := by
    simp [N,routingSeedEncoding,layerEncoding,layerPartsEncoding,BitEncoding.retract,
      LayerResult.identity,BitEncoding.prod_length]
    omega
  have hn : p.1≤N := by omega
  have hlen := stageEncoding.list_length_le p.2
  have hk : (p.2.take i).length≤N := by simp only [List.length_take]; omega
  have hg := fold_growth (p.2.take i) (LayerResult.identity p.1 (List.range p.1))
  simp only [LayerResult.identity,List.length_range,List.length_nil] at hg
  change r.rails.length≤p.1+(p.2.take i).length ∧
    r.variableCount≤p.1+15*(p.2.take i).length*(p.1+(p.2.take i).length+1) ∧
    r.instructions.length≤0+(p.2.take i).length*(p.1+(p.2.take i).length+1) at hg
  have hb : r.Bounded := fold_bounded _ _ (initial_bounded p.1)
  have hR : r.rails.length≤2*N := by
    have h := hg.1
    omega
  have hMC : r.variableCount≤46*(N+1)^2 ∧ r.instructions.length≤3*(N+1)^2 := by
    have h := Nat.mul_le_mul hk (show p.1+(p.2.take i).length+1≤2*N+1 by omega)
    constructor <;> nlinarith [hg.2.1,hg.2.2]
  have hRC : r.rails.length+r.instructions.length+1≤6*(N+1)^2 := by nlinarith [hMC.2]
  have hM : r.variableCount+1≤47*(N+1)^2 := by nlinarith [hMC.1]
  have hprod := Nat.mul_le_mul hM hRC
  have hcode := layer_code_bound r hb
  change (layerEncoding.encode r).length≤(Polynomial.C 100000*(Polynomial.X+1)^4).eval N
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  nlinarith

/-- The finite-control fold implementation receives the actual materialized
initial state and stage-list codeword, rather than a semantic oracle. -/
theorem fp_routingFold : FP routingSeedEncoding layerEncoding
    (fun p => stages p.1 (List.range p.1) p.2) := by
  have h : FP routingSeedEncoding layerEncoding
      (fun p => p.2.foldl advance (.identity p.1 (List.range p.1))) :=
    ⟨ListFoldMachines.computerOn routingSeedEncoding stageEncoding layerEncoding advance
      (fun p => .identity p.1 (List.range p.1)) Prod.snd (fun _ => rfl)
      (Classical.choice fp_advance) (Polynomial.C 100000*(Polynomial.X+1)^4) routing_prefix_size⟩
  exact h.congr (fun p => fold_advance_initial p.1 p.2)

/-- Full serialized instruction generation for an arbitrary numeric formula. -/
theorem fp_program : FP formulaEncoding instructionEncoding.list PositiveRoutingCompiler.program := by
  have hn := fp_fst BitEncoding.unaryNat clauseEncoding.list
  have hseed : FP formulaEncoding routingSeedEncoding (fun f => (f.1,formulaStages f.1 f.2)) :=
    ((hn.comp fp_initialLayer).pair fp_formulaStages).transportOutput (fun _ => rfl)
  exact ((hseed.comp fp_routingFold).comp fp_layerInstructions).congr (fun f => by
    change (stages f.1 (List.range f.1) (formulaStages f.1 f.2)).instructions=_
    rw [stages_formulaStages]
    rfl)

end PlanarHom.PositiveBlockProgram
