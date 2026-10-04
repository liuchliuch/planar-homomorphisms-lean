import PlanarHom.BooleanQuadraticLookup

/-! NEW termination invariant: every processed variable has literal zero linear
coefficient and zero row and column. No rank or normal-form oracle is used. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators

def Cleared (q : Data) (k : ℕ) : Prop :=
  rawLinear q k=false ∧ ∀l,entry q k l=false ∧ entry q l k=false

 theorem pivot_clears_left (q : Data) (i j : ℕ) : Cleared (pivot q i j) i := by
  constructor
  · simp [rawLinear_pivot,keep]
  · intro l
    simp [entry_pivot,keep]
 theorem pivot_clears_right (q : Data) (i j : ℕ) : Cleared (pivot q i j) j := by
  constructor
  · simp [rawLinear_pivot,keep]
  · intro l
    simp [entry_pivot,keep]
 theorem remove_clears (q : Data) (i : ℕ) : Cleared (remove q i) i := by
  constructor
  · simp [rawLinear_remove]
  · intro l
    simp [entry_remove]

 theorem pivot_preserves_cleared (q : Data) (i j k : ℕ) (hk : Cleared q k) :
    Cleared (pivot q i j) k := by
  have hc (a : ℕ) : cross q a k=false := by
    simp [cross,(hk.2 a).1,(hk.2 a).2]
  constructor
  · simp [rawLinear_pivot,hk.1,hc]
  · intro l
    simp [entry_pivot,(hk.2 l).1,(hk.2 l).2,hc]
 theorem remove_preserves_cleared (q : Data) (i k : ℕ) (hk : Cleared q k) :
    Cleared (remove q i) k := by
  constructor
  · simp [rawLinear_remove,hk.1]
  · intro l
    simp [entry_remove,(hk.2 l).1,(hk.2 l).2]
 theorem step_clears (s : State) (i : ℕ) : Cleared (step s i).1 i := by
  unfold step
  split
  · exact pivot_clears_left _ _ _
  · exact remove_clears _ _
 theorem step_preserves_cleared (s : State) (i k : ℕ) (hk : Cleared s.1 k) :
    Cleared (step s i).1 k := by
  unfold step
  split
  · exact pivot_preserves_cleared _ _ _ _ hk
  · exact remove_preserves_cleared _ _ _ hk

 theorem range_cleared (s : State) (t k : ℕ) (hk : k<t) :
    Cleared ((List.range t).foldl step s).1 k := by
  induction t with
  | zero=>omega
  | succ t ih=>
    rw [List.range_succ,List.foldl_append]
    simp only [List.foldl_cons,List.foldl_nil]
    by_cases h:k=t
    · subst k; exact step_clears _ _
    · exact step_preserves_cleared _ _ _ (ih (by omega))

 theorem run_cleared (q : Data) (k : ℕ) (hk : k<dimension q) : Cleared (run q).1 k :=
  range_cleared (q,0,false) (dimension q) k hk

 theorem phase_run (q : Data) (x : Fin (dimension q)→F₂) :
    phase (dimension q) (run q).1 x=bit (run q).1.1 := by
  unfold phase form
  have hl (i:Fin (dimension q)) : bit (rawLinear (run q).1 i.val)=0 := by
    rw [(run_cleared q i.val i.isLt).1,bit_false]
  have ha (i j:Fin (dimension q)) : bit (entry (run q).1 i.val j.val)=0 := by
    rw [((run_cleared q i.val i.isLt).2 j.val).1,bit_false]
  simp only [hl,ha,zero_mul,Finset.sum_const_zero,add_zero]

 theorem gauss_run {K : Type*} [CommRing K] (q : Data) :
    gauss (K:=K) (dimension q) (run q).1=
      BooleanQuadraticGauss.sign (run q).1.1*(2:K)^(dimension q) := by
  simp only [gauss,phase_run,character_bit,Finset.sum_const,Finset.card_univ,
    Fintype.card_fun,Fintype.card_fin,nsmul_eq_mul,
    show Fintype.card F₂=2 from Fintype.card_congr bitEquiv.symm,Nat.cast_pow,Nat.cast_ofNat]
  ring

end PlanarHom.BooleanQuadratic
