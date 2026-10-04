import PlanarHom.NorExactOneCompiler

/-! A polynomial bound for every materialized accumulator and the resulting
actual complete finite-control formula compiler. Unary widths are charged. -/
namespace PlanarHom.NorExactOne
open Complexity CountingCookLevin ParsimoniousNorOneInThree
open PairProjectionMachines ArithmeticCircuitPrimitives

private theorem checkedRef_bound (n z i : ℕ) : checkedRef n z i<n ∨ checkedRef n z i=z := by
  by_cases hi : i<n <;> simp [checkedRef,hi]

/-- Every emitted coordinate is an existing/fresh register or the false fallback. -/
theorem network_refs (gs : NorGates) (n z : ℕ) (c : Clause ℕ) (hc : c∈network n z gs) :
    (c.1<n+4*gs.length ∨ c.1=z) ∧
    (c.2.1<n+4*gs.length ∨ c.2.1=z) ∧
    (c.2.2<n+4*gs.length ∨ c.2.2=z) := by
  induction gs generalizing n with
  | nil => simp [network] at hc
  | cons g gs ih =>
    rcases g with ⟨x,y⟩
    rw [network] at hc
    rcases List.mem_append.mp hc with hc | hc
    · simp only [numericGate,List.mem_cons,List.not_mem_nil,or_false] at hc
      have hx := checkedRef_bound n z x
      have hy := checkedRef_bound n z y
      rcases hc with rfl | rfl | rfl <;> simp only [List.length_cons] <;> omega
    · have h := ih (n+4) hc
      simp only [List.length_cons]
      omega

private theorem nat_length_le (n : ℕ) : (BitEncoding.nat.encode n).length≤n :=
  Complexity.encodeNat_length_le n

private theorem coordinate_length (n z v : ℕ) (h : v<n ∨ v=z) :
    (BitEncoding.nat.encode v).length≤n+(BitEncoding.nat.encode z).length := by
  rcases h with h | rfl
  · exact (nat_length_le v).trans (by omega)
  · omega

theorem network_clause_length (gs : NorGates) (n z : ℕ) (c : Clause ℕ)
    (hc : c∈network n z gs) :
    (clauseEncoding.encode c).length≤5*(n+4*gs.length+(BitEncoding.nat.encode z).length)+2 := by
  have h := network_refs gs n z c hc
  have h1 := coordinate_length _ _ _ h.1
  have h2 := coordinate_length _ _ _ h.2.1
  have h3 := coordinate_length _ _ _ h.2.2
  simp only [clauseEncoding,BitEncoding.prod_length]
  omega

private theorem list_length_exact (f : Formula ℕ) :
    (clauseEncoding.list.encode f).length=2*(BitEncoding.nat.encode f.length).length+1+
      2*(f.map (fun c => (clauseEncoding.encode c).length)).sum+f.length := by
  simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
  omega

theorem appended_network_length (f : Formula ℕ) (gs : NorGates) (n z : ℕ) :
    (clauseEncoding.list.encode (f++network n z gs)).length≤
      3*(clauseEncoding.list.encode f).length+9*gs.length+1+
        6*gs.length*(5*(n+4*gs.length+(BitEncoding.nat.encode z).length)+2) := by
  have hn := nat_length_le (f++network n z gs).length
  have hs := List.sum_le_card_nsmul
    ((network n z gs).map (fun c => (clauseEncoding.encode c).length))
    (5*(n+4*gs.length+(BitEncoding.nat.encode z).length)+2) (by
      intro v hv
      obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hv
      exact network_clause_length gs n z c hc)
  simp only [List.length_map,network_length,smul_eq_mul] at hs
  rw [list_length_exact,list_length_exact]
  simp only [List.map_append,List.sum_append,List.length_append,network_length] at hn ⊢
  ring_nf at hs hn ⊢
  omega

/-- Explicit quadratic growth in the real input word, valid for every fold
prefix and every initial accumulator, including oversized fallback addresses. -/
theorem prefix_size (s : State) (gs : NorGates) (i : ℕ) (hi : i≤gs.length) :
    (stateEncoding.encode ((gs.take i).foldl step s)).length≤
      (Polynomial.C 300*(Polynomial.X+1)^2).eval
        ((stateEncoding.prod gateEncoding.list).encode (s,gs)).length := by
  rcases s with ⟨z,m,f⟩
  let N := ((stateEncoding.prod gateEncoding.list).encode ((z,(m,f)),gs)).length
  let Z := (BitEncoding.nat.encode z).length
  let E := (clauseEncoding.list.encode f).length
  have he : N=2*(2*Z+2*m+E+2)+(gateEncoding.list.encode gs).length+1 := by
    simp [N,Z,E,stateEncoding,formulaEncoding,BitEncoding.prod_length]
    omega
  have hg := gateEncoding.list_length_le gs
  have hk : (gs.take i).length≤N := by simp only [List.length_take]; omega
  have hm : m≤N := by omega
  have hz : Z≤N := by omega
  have hf : E≤N := by omega
  have hb := appended_network_length f (gs.take i) m z
  rw [fold_step]
  change (stateEncoding.encode (z,(m+4*(gs.take i).length,f++network m z (gs.take i)))).length≤
    (Polynomial.C 300*(Polynomial.X+1)^2).eval N
  simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_one]
  conv_lhs => simp only [stateEncoding,formulaEncoding,BitEncoding.prod_length,BitEncoding.unaryNat_length]
  change 2*Z+(2*(m+4*(gs.take i).length)+
    (clauseEncoding.list.encode (f++network m z (gs.take i))).length+1)+1≤300*(N+1)^2
  change (clauseEncoding.list.encode (f++network m z (gs.take i))).length≤
    3*E+9*(gs.take i).length+1+6*(gs.take i).length*(5*(m+4*(gs.take i).length+Z)+2) at hb
  nlinarith [Nat.mul_le_mul hk (show 5*(m+4*(gs.take i).length+Z)+2≤30*N+2 by omega)]

/-- The bounded fold is compiled to a real polynomial-time bit machine. -/
theorem fp_fold : FP (stateEncoding.prod gateEncoding.list) stateEncoding
    (fun p => p.2.foldl step p.1) :=
  ListFoldMachines.fp_foldl gateEncoding stateEncoding step fp_step
    (Polynomial.C 300*(Polynomial.X+1)^2) prefix_size

/-- Complete serialized materialization, with all headers, copied clauses,
binary checks, references, and accumulator growth charged by actual machines. -/
theorem fp_compile : FP CountingNorProgram.encoding formulaEncoding compile := by
  have hn := fp_fst BitEncoding.unaryNat (gateEncoding.list.prod BitEncoding.nat)
  have hgo := fp_snd BitEncoding.unaryNat (gateEncoding.list.prod BitEncoding.nat)
  have hgs := hgo.comp (fp_fst gateEncoding.list BitEncoding.nat)
  have ho := hgo.comp (fp_snd gateEncoding.list BitEncoding.nat)
  have hz := ((hn.comp UnaryNatConversionMachine.fp_conversion).pair
    (fp_const _ BitEncoding.nat 1)).comp BinaryArithmetic.fp_addition
  have hstart := hz.pair (hn.comp fp_ground)
  exact (((hstart.pair hgs).comp fp_fold).pair ho).comp fp_finish

end PlanarHom.NorExactOne
