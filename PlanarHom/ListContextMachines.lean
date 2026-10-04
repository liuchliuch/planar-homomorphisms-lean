import PlanarHom.ListFlattenMachines

/-! # Actual list mapping with a shared typed context -/
namespace PlanarHom.ListContextMachines
open Turing Complexity MachineComposition ArithmeticCircuitPrimitives PairProjectionMachines
open ListFlattenMachines

variable {C α β : Type}

def contextStep (f : C×α→β) (state : C×List β) (a : α) : C×List β :=
  (state.1,state.2++[f (state.1,a)])

theorem fold_contextStep (f : C×α→β) (c : C) (zs : List β) (xs : List α) :
    xs.foldl (contextStep f) (c,zs) = (c,zs++xs.map (fun a => f (c,a))) := by
  induction xs generalizing zs with
  | nil => simp
  | cons a xs ih => simp [contextStep,ih,List.append_assoc]

theorem fp_contextStep (ec : BitEncoding C) (ea : BitEncoding α) (eb : BitEncoding β)
    (f : C×α→β) (hf : FP (ec.prod ea) eb f) :
    FP ((ec.prod eb.list).prod ea) (ec.prod eb.list) (fun p => contextStep f p.1 p.2) := by
  have state := fp_fst (ec.prod eb.list) ea
  have hc := state.comp (fp_fst ec eb.list)
  have hz := state.comp (fp_snd ec eb.list)
  have ha := fp_snd (ec.prod eb.list) ea
  have hvalue := (hc.pair ha).comp hf
  have hsingle := (hvalue.pair (fp_const ((ec.prod eb.list).prod ea) eb.list [])).comp
    (ListMutationMachines.fp_cons eb)
  have hnew := (hz.pair hsingle).comp (ListMutationMachines.fp_append eb)
  exact hc.pair hnew

noncomputable def sizePolynomial {ec : BitEncoding C} {ea : BitEncoding α} {eb : BitEncoding β}
    {f : C×α→β} (body : TM2ComputableInPolyTime (ec.prod ea).toFinEncoding eb.toFinEncoding f) : Polynomial ℕ :=
  Polynomial.C 10*(Polynomial.X+1)*((outputLengthPolynomial body).comp (Polynomial.C 3*Polynomial.X+1)+1)

theorem prefix_size_bound (ec : BitEncoding C) (ea : BitEncoding α) (eb : BitEncoding β)
    (f : C×α→β) (body : TM2ComputableInPolyTime (ec.prod ea).toFinEncoding eb.toFinEncoding f)
    (s : C×List β) (xs : List α) (i : ℕ) :
    ((ec.prod eb.list).encode ((xs.take i).foldl (contextStep f) s)).length ≤
      (sizePolynomial body).eval (((ec.prod eb.list).prod ea.list).encode (s,xs)).length := by
  rcases s with ⟨c,zs⟩
  let N := (((ec.prod eb.list).prod ea.list).encode ((c,zs),xs)).length
  let P := (outputLengthPolynomial body).eval (3*N+1)
  have hN : N=2*(2*(ec.encode c).length+(eb.list.encode zs).length+1)+(ea.list.encode xs).length+1 := by
    simp [N,BitEncoding.prod_length]
  have hx : (ea.list.encode xs).length=2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun a => (ea.encode a).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hc : (ec.encode c).length≤N := by omega
  have hz : (eb.list.encode zs).length≤N := by omega
  have hn : xs.length≤N := by omega
  have hin (a : α) (ha : a∈xs) : (ea.encode a).length≤N := by
    have h := ListMapMachines.mem_le_sum_map (fun a => (ea.encode a).length) ha
    dsimp only at h
    omega
  have hout (a : α) (ha : a∈xs) : (eb.encode (f (c,a))).length≤P := by
    apply (encoded_output_length_le body (c,a)).trans
    apply natPolynomial_monotone
    change ((ec.prod ea).encode (c,a)).length≤3*N+1
    rw [BitEncoding.prod_length]
    dsimp only
    have h := hin a ha
    omega
  have htake : (xs.take i).length≤N := by rw [List.length_take]; exact (Nat.min_le_right i xs.length).trans hn
  have hsum : ((xs.take i).map (fun a => (eb.encode (f (c,a))).length)).sum≤N*P :=
    (ListMapMachines.sum_map_le_mul _ _ P (fun a ha => hout a (List.mem_of_mem_take ha))).trans
      (Nat.mul_le_mul_right P htake)
  have hp : payloadSize eb ((xs.take i).map (fun a => f (c,a)))≤2*N*P+N := by
    simp only [payloadSize_eq,List.length_map,List.map_map,Function.comp_def]
    nlinarith
  have hz' : payloadSize eb zs≤N := (payloadSize_le_word eb zs).trans hz
  have hw := word_length_le_payload eb (zs++(xs.take i).map (fun a => f (c,a)))
  rw [payloadSize_append] at hw
  rw [fold_contextStep,BitEncoding.prod_length]
  simp only [sizePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change 2*(ec.encode c).length+(eb.list.encode (zs++(xs.take i).map (fun a => f (c,a)))).length+1≤
    10*(N+1)*(P+1)
  nlinarith

/-- Map a genuine typed FP body while retaining the same materialized context
for every element; context copying and all list updates are real machines. -/
theorem fp_mapWithContext (ec : BitEncoding C) (ea : BitEncoding α) (eb : BitEncoding β)
    (f : C×α→β) (hf : FP (ec.prod ea) eb f) :
    FP (ec.prod ea.list) eb.list (fun p => p.2.map (fun a => f (p.1,a))) := by
  obtain ⟨body⟩ := hf
  have step := fp_contextStep ec ea eb f ⟨body⟩
  have fold := ListFoldMachines.fp_foldl ea (ec.prod eb.list) (contextStep f) step (sizePolynomial body)
    (fun s xs i _ => prefix_size_bound ec ea eb f body s xs i)
  have hc := fp_fst ec ea.list
  have hx := fp_snd ec ea.list
  have init := (hc.pair (fp_const (ec.prod ea.list) eb.list [])).pair hx
  exact ((init.comp fold).comp (fp_snd ec eb.list)).congr (fun p => by
    simp only [Function.comp_apply,fold_contextStep,List.nil_append])

end PlanarHom.ListContextMachines
