import PlanarHom.BooleanQuadraticRemoveSemantics

/-! NEW full semantic invariant and correctness of the executable quadratic
normalizer. This theorem has no supplied elimination certificate. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators
variable {K : Type*} [Field K] [CharZero K]

def scaled (n : ℕ) (s : State) : K :=
  if s.2.2 then 0 else gauss n s.1/(2:K)^s.2.1

 theorem scaled_step (n : ℕ) (s : State) (hn : dimension s.1=n) (i : ℕ) (hi:i<n)
    (hl : ∀ k < i,Cleared s.1 k) : scaled (K:=K) n (step s i)=scaled n s := by
  unfold step
  cases hp:partner s.1 i with
  | some j=>
    obtain ⟨hij,hj,hc⟩:=partner_some s.1 i j hp
    rw [hn] at hj
    have h:=gauss_pivot (K:=K) s.1 hn ⟨i,hi⟩ ⟨j,hj⟩ (by intro he; have hh : j=i := congrArg Fin.val he; omega) hc
    simp only [scaled]
    cases hz:s.2.2
    · simp only [Bool.false_eq_true,ite_false]
      rw [←h,pow_succ]
      have htwo:(2:K)≠0:=by norm_num
      field_simp
    · rfl
  | none=>
    have hc:=partner_none_cross s.1 i hp hl
    have h:=gauss_remove (K:=K) s.1 hn ⟨i,hi⟩ (by
      intro k hk
      exact hc k.val (by simpa [hn] using k.isLt) (by simpa [Fin.ext_iff] using hk))
    simp only [scaled]
    cases hz:s.2.2 <;> cases hb:linear s.1 i <;> simp_all

 theorem scaled_range (q : Data) (t : ℕ) (ht:t≤dimension q) :
    scaled (K:=K) (dimension q) ((List.range t).foldl step (q,0,false))=gauss (dimension q) q := by
  induction t with
  | zero=>simp [scaled]
  | succ t ih=>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    rw [scaled_step (dimension q) _ (fold_dimension (List.range t) (q,0,false)) t (by omega)
      (fun k hk=>range_cleared (q,0,false) t k hk)]
    exact ih (by omega)

 theorem result_eq_gauss (q : Data) : result (K:=K) q=gauss (dimension q) q := by
  have h:=scaled_range (K:=K) q (dimension q) le_rfl
  change scaled (dimension q) (run q)=_ at h
  rw [←h]
  unfold result scaled
  dsimp only
  cases hb:(run q).2.2
  · simp only [Bool.false_eq_true,ite_false]
    rw [gauss_run]
    have hp:=run_pairs_bound q
    have he:(2:K)^(dimension q)=(2:K)^(dimension q-(run q).2.1)*(2:K)^(run q).2.1 := by
      rw [←pow_add,Nat.sub_add_cancel hp]
    rw [he]
    have hn:(2:K)^(run q).2.1≠0:=pow_ne_zero _ (by norm_num)
    field_simp
  · rfl

end PlanarHom.BooleanQuadratic
