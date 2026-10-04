import PlanarHom.FixedFieldArithmeticMachines
import PlanarHom.ListContextMachines

/-! # Actual multiplication of ascending coefficient lists by one linear factor -/
namespace PlanarHom.LinearFactorCoefficientMachines
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines MachineComposition
open ListFlattenMachines
variable {K : Type} [Field K]

def go (μ prev : K) : List K→List K
  | [] => [prev]
  | a::cs => (prev-μ*a)::go μ a cs

def mulLinear (μ : K) (cs : List K) : List K := go μ 0 cs

def emitted (μ prev : K) : List K→List K
  | [] => []
  | a::cs => (prev-μ*a)::emitted μ a cs

def lastValue (prev : K) : List K→K
  | [] => prev
  | a::cs => lastValue a cs

@[simp] theorem go_length (μ prev : K) (cs : List K) : (go μ prev cs).length=cs.length+1 := by
  induction cs generalizing prev with
  | nil => rfl
  | cons a cs ih => simp [go,ih]

@[simp] theorem mulLinear_length (μ : K) (cs : List K) : (mulLinear μ cs).length=cs.length+1 := go_length _ _ _

@[simp] theorem emitted_length (μ prev : K) (cs : List K) : (emitted μ prev cs).length=cs.length := by
  induction cs generalizing prev with
  | nil => rfl
  | cons a cs ih => simp [emitted,ih]

theorem go_eq_emitted_last (μ prev : K) (cs : List K) :
    go μ prev cs=emitted μ prev cs++[lastValue prev cs] := by
  induction cs generalizing prev with
  | nil => rfl
  | cons a cs ih => simp [go,emitted,lastValue,ih]

/-- Ascending coefficient semantics, including all explicit trailing zeroes. -/
noncomputable def coefficientPolynomial : List K→Polynomial K
  | [] => 0
  | a::cs => Polynomial.C a+Polynomial.X*coefficientPolynomial cs

/-- The explicit list position is the corresponding polynomial coefficient. -/
theorem coefficientPolynomial_coeff (cs : List K) (i : ℕ) :
    (coefficientPolynomial cs).coeff i = cs[i]?.getD 0 := by
  induction cs generalizing i with
  | nil => simp [coefficientPolynomial]
  | cons a cs ih =>
    cases i with
    | zero => simp [coefficientPolynomial]
    | succ i => simp [coefficientPolynomial,Polynomial.coeff_add,ih]

theorem coefficientPolynomial_go (μ prev : K) (cs : List K) :
    coefficientPolynomial (go μ prev cs)=Polynomial.C prev+
      (Polynomial.X-Polynomial.C μ)*coefficientPolynomial cs := by
  induction cs generalizing prev with
  | nil => simp [go,coefficientPolynomial]
  | cons a cs ih =>
    simp only [go,coefficientPolynomial,ih,map_sub,map_mul]
    ring

theorem coefficientPolynomial_mulLinear (μ : K) (cs : List K) :
    coefficientPolynomial (mulLinear μ cs)=(Polynomial.X-Polynomial.C μ)*coefficientPolynomial cs := by
  simpa [mulLinear] using coefficientPolynomial_go μ 0 cs

def coefficient (p : K×(K×K)) : K := p.2.1-p.1*p.2.2

def stateStep (s : K×(K×List K)) (a : K) : K×(K×List K) :=
  (s.1,(a,s.2.2++[s.2.1-s.1*a]))

def finish (s : K×(K×List K)) : List K := s.2.2++[s.2.1]

theorem fold_stateStep (μ prev : K) (zs cs : List K) :
    cs.foldl stateStep (μ,(prev,zs))=(μ,(lastValue prev cs,zs++emitted μ prev cs)) := by
  induction cs generalizing prev zs with
  | nil => simp [lastValue,emitted]
  | cons a cs ih => simp [stateStep,lastValue,emitted,ih,List.append_assoc]

theorem finish_fold (μ prev : K) (zs cs : List K) :
    finish (cs.foldl stateStep (μ,(prev,zs)))=zs++go μ prev cs := by
  rw [fold_stateStep]
  simp [finish,go_eq_emitted_last,List.append_assoc]

variable [Algebra ℚ K] {dimension : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)

noncomputable abbrev fieldEncoding := numberFieldEncoding basis
noncomputable abbrev stateEncoding := (fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis).list)

theorem fp_coefficient : FP ((fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis)))
    (fieldEncoding basis) coefficient := by
  have hm := fp_fst (fieldEncoding basis) ((fieldEncoding basis).prod (fieldEncoding basis))
  have ht := fp_snd (fieldEncoding basis) ((fieldEncoding basis).prod (fieldEncoding basis))
  have hp := ht.comp (fp_fst (fieldEncoding basis) (fieldEncoding basis))
  have ha := ht.comp (fp_snd (fieldEncoding basis) (fieldEncoding basis))
  have hmul := (hm.pair ha).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact (hp.pair hmul).comp (FixedFieldArithmetic.fp_subtraction basis)

theorem fp_stateStep : FP ((stateEncoding basis).prod (fieldEncoding basis)) (stateEncoding basis)
    (fun p => stateStep p.1 p.2) := by
  have hs := fp_fst (stateEncoding basis) (fieldEncoding basis)
  have hm := hs.comp (fp_fst (fieldEncoding basis) ((fieldEncoding basis).prod (fieldEncoding basis).list))
  have ht := hs.comp (fp_snd (fieldEncoding basis) ((fieldEncoding basis).prod (fieldEncoding basis).list))
  have hp := ht.comp (fp_fst (fieldEncoding basis) (fieldEncoding basis).list)
  have hz := ht.comp (fp_snd (fieldEncoding basis) (fieldEncoding basis).list)
  have ha := fp_snd (stateEncoding basis) (fieldEncoding basis)
  have hv := (hm.pair (hp.pair ha)).comp (fp_coefficient basis)
  have hsingle := (hv.pair (fp_const ((stateEncoding basis).prod (fieldEncoding basis)) (fieldEncoding basis).list [])).comp
    (ListMutationMachines.fp_cons (fieldEncoding basis))
  have hout := (hz.pair hsingle).comp (ListMutationMachines.fp_append (fieldEncoding basis))
  exact hm.pair (ha.pair hout)

theorem fp_finish : FP (stateEncoding basis) (fieldEncoding basis).list finish := by
  have ht := fp_snd (fieldEncoding basis) ((fieldEncoding basis).prod (fieldEncoding basis).list)
  have hp := ht.comp (fp_fst (fieldEncoding basis) (fieldEncoding basis).list)
  have hz := ht.comp (fp_snd (fieldEncoding basis) (fieldEncoding basis).list)
  have hsingle := (hp.pair (fp_const (stateEncoding basis) (fieldEncoding basis).list [])).comp
    (ListMutationMachines.fp_cons (fieldEncoding basis))
  exact (hz.pair hsingle).comp (ListMutationMachines.fp_append (fieldEncoding basis))

noncomputable def sizePolynomial (body : Turing.TM2ComputableInPolyTime
    ((fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis))).toFinEncoding
    (fieldEncoding basis).toFinEncoding coefficient) : Polynomial ℕ :=
  Polynomial.C 12*(Polynomial.X+1)*((outputLengthPolynomial body).comp (Polynomial.C 5*Polynomial.X+Polynomial.C 2)+1)

omit [Field K] [Algebra ℚ K] in
theorem lastValue_length_bound (e : BitEncoding K) (N : ℕ) (prev : K) (cs : List K)
    (hp : (e.encode prev).length≤N) (hcs : ∀a∈cs,(e.encode a).length≤N) :
    (e.encode (lastValue prev cs)).length≤N := by
  induction cs generalizing prev with
  | nil => exact hp
  | cons a cs ih => exact ih a (hcs a (by simp)) (fun b hb => hcs b (by simp [hb]))

theorem emitted_length_bound (body : Turing.TM2ComputableInPolyTime
    ((fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis))).toFinEncoding
    (fieldEncoding basis).toFinEncoding coefficient) (N : ℕ) (μ prev : K) (cs : List K)
    (hm : ((fieldEncoding basis).encode μ).length≤N) (hp : ((fieldEncoding basis).encode prev).length≤N)
    (hcs : ∀a∈cs,((fieldEncoding basis).encode a).length≤N) :
    ∀b∈emitted μ prev cs,((fieldEncoding basis).encode b).length≤(outputLengthPolynomial body).eval (5*N+2) := by
  induction cs generalizing prev with
  | nil => simp [emitted]
  | cons a cs ih =>
    intro b hb
    rcases List.mem_cons.mp hb with rfl|hb
    · have h := encoded_output_length_le body (μ,(prev,a))
      apply h.trans
      apply natPolynomial_monotone
      change (((fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis))).encode (μ,(prev,a))).length≤5*N+2
      simp only [BitEncoding.prod_length]
      have ha := hcs a (by simp)
      omega
    · exact ih a (hcs a (by simp)) (fun b hb => hcs b (by simp [hb])) b hb

theorem prefix_size_bound (body : Turing.TM2ComputableInPolyTime
    ((fieldEncoding basis).prod ((fieldEncoding basis).prod (fieldEncoding basis))).toFinEncoding
    (fieldEncoding basis).toFinEncoding coefficient) (s : K×(K×List K)) (cs : List K) (i : ℕ) :
    ((stateEncoding basis).encode ((cs.take i).foldl stateStep s)).length≤
      (sizePolynomial basis body).eval (((stateEncoding basis).prod (fieldEncoding basis).list).encode (s,cs)).length := by
  rcases s with ⟨μ,prev,zs⟩
  let e := fieldEncoding basis
  let N := (((stateEncoding basis).prod e.list).encode ((μ,(prev,zs)),cs)).length
  let P := (outputLengthPolynomial body).eval (5*N+2)
  have hN : N=2*(2*(e.encode μ).length+(2*(e.encode prev).length+(e.list.encode zs).length+1)+1)+(e.list.encode cs).length+1 := by
    simp [N,stateEncoding,e,BitEncoding.prod_length]
  have hx : (e.list.encode cs).length=2*(BitEncoding.nat.encode cs.length).length+1+
      2*(cs.map (fun a => (e.encode a).length)).sum+cs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  have hm : (e.encode μ).length≤N := by omega
  have hp : (e.encode prev).length≤N := by omega
  have hz : (e.list.encode zs).length≤N := by omega
  have hn : cs.length≤N := by omega
  have hin (a : K) (ha : a∈cs) : (e.encode a).length≤N := by
    have h := ListMapMachines.mem_le_sum_map (fun a => (e.encode a).length) ha
    dsimp only at h
    omega
  have htinput (a : K) (ha : a∈cs.take i) : (e.encode a).length≤N := hin a (List.mem_of_mem_take ha)
  have hlast := lastValue_length_bound e N prev (cs.take i) hp htinput
  have hout := emitted_length_bound basis body N μ prev (cs.take i) hm hp htinput
  have htlen : (emitted μ prev (cs.take i)).length≤N := by
    rw [emitted_length,List.length_take]
    exact (Nat.min_le_right i cs.length).trans hn
  have hsum : ((emitted μ prev (cs.take i)).map (fun a => (e.encode a).length)).sum≤N*P :=
    (ListMapMachines.sum_map_le_mul _ _ P hout).trans (Nat.mul_le_mul_right P htlen)
  have hemp : payloadSize e (emitted μ prev (cs.take i))≤2*N*P+N := by
    rw [payloadSize_eq]
    nlinarith
  have hzp : payloadSize e zs≤N := (payloadSize_le_word e zs).trans hz
  have hw := word_length_le_payload e (zs++emitted μ prev (cs.take i))
  rw [payloadSize_append] at hw
  rw [fold_stateStep]
  conv_lhs => simp only [stateEncoding,BitEncoding.prod_length]
  simp only [sizePolynomial,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_C,
    Polynomial.eval_X,Polynomial.eval_one,Polynomial.eval_comp]
  change 2*(e.encode μ).length+(2*(e.encode (lastValue prev (cs.take i))).length+
      (e.list.encode (zs++emitted μ prev (cs.take i))).length+1)+1≤12*(N+1)*(P+1)
  nlinarith

/-- Every coefficient is obtained by actual fixed-field arithmetic on μ and two
original input coefficients; no unbounded fold-growth hypothesis is assumed. -/
theorem fp_mulLinear : FP ((fieldEncoding basis).prod (fieldEncoding basis).list) (fieldEncoding basis).list
    (fun p => mulLinear p.1 p.2) := by
  obtain ⟨body⟩ := fp_coefficient basis
  have hf := ListFoldMachines.fp_foldl (fieldEncoding basis) (stateEncoding basis) stateStep (fp_stateStep basis)
    (sizePolynomial basis body) (fun s cs i _ => prefix_size_bound basis body s cs i)
  let input := (fieldEncoding basis).prod (fieldEncoding basis).list
  have hm := fp_fst (fieldEncoding basis) (fieldEncoding basis).list
  have hcs := fp_snd (fieldEncoding basis) (fieldEncoding basis).list
  have hz := (fp_const input (fieldEncoding basis) 0).pair (fp_const input (fieldEncoding basis).list [])
  have hi := (hm.pair hz).pair hcs
  exact ((hi.comp hf).comp (fp_finish basis)).congr (fun p => by
    simpa [mulLinear] using finish_fold p.1 0 [] p.2)

end PlanarHom.LinearFactorCoefficientMachines
