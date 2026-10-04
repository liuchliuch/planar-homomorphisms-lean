import PlanarHom.PlanarityParityMachines

/-! NEW polynomial encoded-size bounds and actual FP elimination program. -/
namespace PlanarHom.PlanarityParitySolver
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ListFlattenMachines Polynomial

def BoundedState (N : ℕ) (s : ForwardState) : Prop :=
  s.1.1.length + s.1.2.length ≤ N ∧
    ∀ e ∈ s.1.1 ++ s.1.2, (natCode.encode e.1).length ≤ N ∧
      (natCode.encode e.2.1).length ≤ N

theorem boundedState_mono {M N : ℕ} {s : ForwardState} (h : BoundedState M s) (hMN : M ≤ N) :
    BoundedState N s := ⟨h.1.trans hMN,fun e he => ⟨(h.2 e he).1.trans hMN,(h.2 e he).2.trans hMN⟩⟩

theorem encoded_element_le {A : Type} (code : BitEncoding A) {xs : List A} {x : A} (hx : x ∈ xs) :
    (code.encode x).length ≤ (code.list.encode xs).length := by
  have hsum := List.single_le_sum (l := xs.map (fun a => (code.encode a).length)) (fun y _ => Nat.zero_le y) (code.encode x).length
    (List.mem_map.mpr ⟨x,hx,rfl⟩)
  have hp := payloadSize_le_word code xs
  rw [payloadSize_eq] at hp
  omega

theorem constraint_width (e : Constraint) :
    (natCode.encode e.1).length ≤ (constraintCode.encode e).length ∧
    (natCode.encode e.2.1).length ≤ (constraintCode.encode e).length := by
  simp only [constraintCode,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
  omega

theorem boundedState_initial (s : ForwardState) : BoundedState (forwardCode.encode s).length s := by
  have hlen₁ := BitEncoding.list_length_le constraintCode s.1.1
  have hlen₂ := BitEncoding.list_length_le constraintCode s.1.2
  have hcode : (forwardCode.encode s).length =
      4*(constraintCode.list.encode s.1.1).length + 2*(constraintCode.list.encode s.1.2).length + 4 := by
    simp only [forwardCode,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
    omega
  constructor
  · omega
  · intro e he
    have hw := constraint_width e
    rcases List.mem_append.mp he with he | he
    · have h := encoded_element_le constraintCode he
      constructor <;> omega
    · have h := encoded_element_le constraintCode he
      constructor <;> omega

theorem boundedState_step {N : ℕ} {s : ForwardState} (h : BoundedState N s) (tick : Constraint) :
    BoundedState N (forwardStep s tick) := by
  rcases s with ⟨⟨es,log⟩,ok⟩
  cases es with
  | nil => exact h
  | cons e tail =>
    rcases e with ⟨u,v,b⟩
    have huv := h.2 (u,v,b) (by simp)
    have htail : ∀ e ∈ tail ++ log, (natCode.encode e.1).length ≤ N ∧
        (natCode.encode e.2.1).length ≤ N := fun e he => h.2 e (by simpa using Or.inr he)
    simp only [forwardStep]
    split_ifs with he
    · constructor
      · change tail.length + log.length ≤ N
        have hh := h.1
        simp only [List.length_cons] at hh
        omega
      · exact htail
    · constructor
      · simpa only [List.length_map,List.length_cons,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h.1
      · intro e hem
        rcases List.mem_append.mp hem with hem | hem
        · obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hem
          have hcN := htail c (List.mem_append_left _ hc)
          simp only [substitute]
          constructor
          · split_ifs <;> first | exact huv.2 | exact hcN.1
          · split_ifs <;> first | exact huv.2 | exact hcN.2
        · rcases List.mem_cons.mp hem with rfl | hem
          · exact huv
          · exact htail e (List.mem_append_right _ hem)

theorem boundedState_fold {N : ℕ} {s : ForwardState} (h : BoundedState N s) (ticks : List Constraint) :
    BoundedState N (ticks.foldl forwardStep s) := by
  induction ticks generalizing s with
  | nil => exact h
  | cons e ticks ih => exact ih (boundedState_step h e)

theorem constraint_list_size (N : ℕ) (es : List Constraint)
    (hlen : es.length ≤ N)
    (hwidth : ∀ e ∈ es, (natCode.encode e.1).length ≤ N ∧ (natCode.encode e.2.1).length ≤ N) :
    (constraintCode.list.encode es).length ≤ 24*N^2+21*N+1 := by
  have hcode : ∀ e ∈ es, (constraintCode.encode e).length ≤ 4*N+3 := by
    intro e he
    have hw := hwidth e he
    simp only [constraintCode,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
    omega
  have hsum := List.sum_le_card_nsmul (es.map (fun e => (constraintCode.encode e).length)) (4*N+3)
    (by intro k hk; obtain ⟨e,he,rfl⟩ := List.mem_map.mp hk; exact hcode e he)
  simp only [List.length_map,smul_eq_mul] at hsum
  have hm := Nat.mul_le_mul_right (4*N+3) hlen
  have hp := word_length_le_payload constraintCode es
  rw [payloadSize_eq] at hp
  nlinarith

theorem boundedState_size {N : ℕ} {s : ForwardState} (h : BoundedState N s) :
    (forwardCode.encode s).length ≤ 200*(N+1)^2 := by
  have hp := constraint_list_size N s.1.1 (by have := h.1; omega)
    (fun e he => h.2 e (List.mem_append_left _ he))
  have hl := constraint_list_size N s.1.2 (by have := h.1; omega)
    (fun e he => h.2 e (List.mem_append_right _ he))
  simp only [forwardCode,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
  nlinarith

/-- Actual polynomial-time forward elimination on the exact dynamic list codec. -/
theorem fp_forwardRun : FP constraintCode.list forwardCode forwardRun := by
  have hfold := ListFoldMachines.fp_foldl constraintCode forwardCode forwardStep fp_forwardStep
    (C 200*(X+1)^2) (by
      intro s ticks k _
      have hn : (forwardCode.encode s).length ≤
          ((forwardCode.prod constraintCode.list).encode (s,ticks)).length := by
        simp only [BitEncoding.prod_length]
        omega
      have hb := boundedState_fold (boundedState_mono (boundedState_initial s) hn) (ticks.take k)
      simpa only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,
        Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one] using boundedState_size hb)
  have hs := ((fp_id constraintCode.list).pair (fp_const _ constraintCode.list [])).pair
    (fp_const _ BitEncoding.bool true)
  exact (hs.pair (fp_id constraintCode.list)).comp hfold

/-- A backward substitution appends only one bounded-size label/Boolean binding. -/
theorem backStep_payload (xs : Assignment) (e : Constraint) :
    payloadSize (natCode.prod BitEncoding.bool) (backStep xs e) ≤
      payloadSize (natCode.prod BitEncoding.bool) xs + 2*(constraintCode.encode e).length+1 := by
  simp only [backStep,payloadSize_eq,List.map_cons,List.sum_cons,List.length_cons,
    BitEncoding.prod_length,BitEncoding.bool,List.length_singleton,constraintCode]
  omega

theorem replayFold_payload (xs : Assignment) (es : List Constraint) :
    payloadSize (natCode.prod BitEncoding.bool) (es.foldl backStep xs) ≤
      payloadSize (natCode.prod BitEncoding.bool) xs + payloadSize constraintCode es := by
  induction es generalizing xs with
  | nil => simp [payloadSize_eq]
  | cons e es ih =>
    have hi := ih (backStep xs e)
    have hs := backStep_payload xs e
    simp only [List.foldl_cons]
    have hp : payloadSize constraintCode (e::es) =
        2*(constraintCode.encode e).length+1+payloadSize constraintCode es := by
      simp only [payloadSize_eq,List.map_cons,List.sum_cons,List.length_cons]
      omega
    rw [hp]
    omega

theorem fp_replay : FP constraintCode.list assignmentCode replay := by
  have hfold := ListFoldMachines.fp_foldl constraintCode assignmentCode backStep fp_backStep
    (C 3*X+1) (by
      intro xs es k _
      have hpay := replayFold_payload xs (es.take k)
      have ht : payloadSize constraintCode (es.take k) ≤ payloadSize constraintCode es := by
        have h := payloadSize_append constraintCode (es.take k) (es.drop k)
        rw [List.take_append_drop] at h
        omega
      have hx := payloadSize_le_word (natCode.prod BitEncoding.bool) xs
      change payloadSize (natCode.prod BitEncoding.bool) xs ≤ (assignmentCode.encode xs).length at hx
      have he := payloadSize_le_word constraintCode es
      have hw := word_length_le_payload (natCode.prod BitEncoding.bool) ((es.take k).foldl backStep xs)
      simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
        Polynomial.eval_one,BitEncoding.prod_length]
      change _ ≤ 3*(2*(assignmentCode.encode xs).length+(constraintCode.list.encode es).length+1)+1
      change (assignmentCode.encode _).length ≤ _ at hw
      omega)
  exact ((fp_const constraintCode.list assignmentCode []).pair (fp_id constraintCode.list)).comp hfold

/-- A total polynomial-time machine computes both the decision and its actual
satisfying Boolean assignment. This theorem does not claim planar embedding. -/
theorem fp_computed : FP constraintCode.list (BitEncoding.bool.prod assignmentCode) computed := by
  have hf := fp_forwardRun
  have hok := hf.comp (fp_snd (constraintCode.list.prod constraintCode.list) BitEncoding.bool)
  have hlog := (hf.comp (fp_fst (constraintCode.list.prod constraintCode.list) BitEncoding.bool)).comp
    (fp_snd constraintCode.list constraintCode.list)
  exact hok.pair (hlog.comp fp_replay)

end PlanarHom.PlanarityParitySolver
