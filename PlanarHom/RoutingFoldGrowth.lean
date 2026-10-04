import PlanarHom.RoutingStageMachines

/-! Explicit reachable-state growth for the actual stage fold. Bounds are
proved on every typed stage script, including off-promise branch indices. -/
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousBlockTemplate

def Instruction.Bounded (B : ℕ) (op : Instruction) : Prop := op.2.1≤B ∧ op.2.2.1≤B ∧ op.2.2.2≤B

def LayerResult.Bounded (r : LayerResult) : Prop :=
  (∀x∈r.rails,x≤r.variableCount) ∧ (∀op∈r.instructions,op.Bounded r.variableCount)

structure LayerResult.Growth (m : ℕ) (r : LayerResult) : Prop where
  increases : m≤r.variableCount
  bounded : r.Bounded

theorem Instruction.Bounded.mono {B C : ℕ} {op : Instruction} (h : op.Bounded B) (hBC : B≤C) : op.Bounded C := by
  rcases h with ⟨h1,h2,h3⟩
  exact ⟨h1.trans hBC,h2.trans hBC,h3.trans hBC⟩

theorem passive_growth (m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x≤m) : (passive m rs).Growth m := by
  refine ⟨by change m≤m+6*rs.length; omega,?_,?_⟩
  · intro x hx
    exact (wireRails_bounds m rs x hx).2.le
  · intro op hop
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hop
    change x≤m+6*rs.length ∧ 0≤m+6*rs.length ∧ 0≤m+6*rs.length
    exact ⟨(hr x hx).trans (by omega),Nat.zero_le _,Nat.zero_le _⟩

theorem prependBlock_growth (m : ℕ) (op : Instruction) (outs : List ℕ) (r : LayerResult)
    (hop : op.Bounded m) (hout : ∀x∈outs,x≤m+op.1.template.fresh)
    (hr : r.Growth (m+op.1.template.fresh)) : (prependBlock op outs r).Growth m := by
  have hm : m≤r.variableCount := by have h := hr.increases; omega
  refine ⟨hm,?_,?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · exact (hout x hx).trans hr.increases
    · exact hr.bounded.1 x hx
  · intro q hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact hop.mono hm
    · exact hr.bounded.2 q hq

theorem swapLayer_growth (i m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x≤m) : (swapLayer m i rs).Growth m := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => exact passive_growth m [] hr
    | cons a rs =>
      cases rs with
      | nil => exact passive_growth m [a] hr
      | cons b rs =>
        exact prependBlock_growth m (crossing a b) [m,m+1] (passive (m+15) rs)
          ⟨hr b (by simp),hr a (by simp),Nat.zero_le _⟩
          (by intro x hx; change x≤m+15; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega)
          (passive_growth (m+15) rs (fun x hx => (hr x (by simp [hx])).trans (by omega)))
  | succ i ih =>
    cases rs with
    | nil => exact passive_growth m [] hr
    | cons a rs =>
      exact prependBlock_growth m (wire a) [m] (swapLayer (m+6) i rs)
        ⟨hr a (by simp),Nat.zero_le _,Nat.zero_le _⟩
        (by intro x hx; change x≤m+6; simp only [List.mem_singleton] at hx; omega)
        (ih (m+6) rs (fun x hx => (hr x (by simp [hx])).trans (by omega)))

theorem copyLayer_growth (i m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x≤m) : (copyLayer m i rs).Growth m := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => exact passive_growth m [] hr
    | cons a rs =>
      exact prependBlock_growth m (fan a) [m+1,m] (passive (m+12) rs)
        ⟨hr a (by simp),Nat.zero_le _,Nat.zero_le _⟩
        (by intro x hx; change x≤m+12; simp only [List.mem_cons,List.not_mem_nil,or_false] at hx; omega)
        (passive_growth (m+12) rs (fun x hx => (hr x (by simp [hx])).trans (by omega)))
  | succ i ih =>
    cases rs with
    | nil => exact passive_growth m [] hr
    | cons a rs =>
      exact prependBlock_growth m (wire a) [m] (copyLayer (m+6) i rs)
        ⟨hr a (by simp),Nat.zero_le _,Nat.zero_le _⟩
        (by intro x hx; change x≤m+6; simp only [List.mem_singleton] at hx; omega)
        (ih (m+6) rs (fun x hx => (hr x (by simp [hx])).trans (by omega)))

theorem getRef_le (rs : List ℕ) (i m : ℕ) (hr : ∀x∈rs,x≤m) : getRef rs i≤m := by
  by_cases hi : i<rs.length
  · exact hr _ (getRef_mem rs i hi)
  · simp [getRef,List.getElem?_eq_none (by omega : rs.length ≤ i)]

theorem checkLayer_growth (n m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x≤m) : (checkLayer n m rs).Growth m := by
  have hp := passive_growth m (rs.take n) (fun x hx => hr x (List.mem_of_mem_take hx))
  refine ⟨hp.increases,hp.bounded.1,?_⟩
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · exact hp.bounded.2 op hop
  · have he := List.mem_singleton.mp hop
    subst op
    exact ⟨(getRef_le rs n m hr).trans hp.increases,(getRef_le rs (n+1) m hr).trans hp.increases,
      (getRef_le rs (n+2) m hr).trans hp.increases⟩

theorem Stage.render_growth (s : Stage) (m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x≤m) : (s.render m rs).Growth m := by
  cases s with
  | swap i => exact swapLayer_growth i m rs hr
  | copy i => exact copyLayer_growth i m rs hr
  | check n => exact checkLayer_growth n m rs hr

theorem advance_bounded (r : LayerResult) (s : Stage) (hr : r.Bounded) : (advance r s).Bounded := by
  have hn := s.render_growth r.variableCount r.rails hr.1
  refine ⟨hn.bounded.1,?_⟩
  intro op hop
  rcases List.mem_append.mp hop with hop | hop
  · exact (hr.2 op hop).mono hn.increases
  · exact hn.bounded.2 op hop

theorem Stage.render_rails_bound (s : Stage) (m : ℕ) (rs : List ℕ) : (s.render m rs).rails.length≤rs.length+1 := by
  cases s with
  | swap i => simp [Stage.render]
  | copy i => exact copyLayer_rails_length_le i m rs
  | check n => simp [Stage.render,checkLayer,wireRails_length,List.length_take]

theorem Stage.render_code_bound (s : Stage) (m : ℕ) (rs : List ℕ) : (s.render m rs).instructions.length≤rs.length+1 := by
  cases s with
  | swap i => exact (swapLayer_instructions_length i m rs).trans (by omega)
  | copy i => simp [Stage.render,copyLayer_instructions_length]
  | check n => simp [Stage.render,checkLayer_instructions_length,List.length_take]

theorem swapLayer_header_bound (i m : ℕ) (rs : List ℕ) : (swapLayer m i rs).variableCount≤m+15*rs.length := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [swapLayer,passive]
    | cons a rs => cases rs <;> simp [swapLayer,passive] <;> omega
  | succ i ih =>
    cases rs with
    | nil => simp [swapLayer,passive]
    | cons a rs => have h := ih (m+6) rs; simp only [swapLayer,List.length_cons]; omega

theorem copyLayer_header_bound (i m : ℕ) (rs : List ℕ) : (copyLayer m i rs).variableCount≤m+15*rs.length := by
  induction i generalizing m rs with
  | zero => cases rs <;> simp [copyLayer,passive] <;> omega
  | succ i ih =>
    cases rs with
    | nil => simp [copyLayer,passive]
    | cons a rs => have h := ih (m+6) rs; simp only [copyLayer,List.length_cons]; omega

theorem Stage.render_header_bound (s : Stage) (m : ℕ) (rs : List ℕ) :
    (s.render m rs).variableCount≤m+15*(rs.length+1) := by
  cases s with
  | swap i => exact (swapLayer_header_bound i m rs).trans (by omega)
  | copy i => exact (copyLayer_header_bound i m rs).trans (by omega)
  | check n => simp [Stage.render,checkLayer,List.length_take]; omega

theorem fold_bounded (ss : List Stage) (r : LayerResult) (hr : r.Bounded) : (ss.foldl advance r).Bounded := by
  induction ss generalizing r with
  | nil => exact hr
  | cons s ss ih => exact ih (advance r s) (advance_bounded r s hr)

/-- Every prefix state has polynomial counts, irrespective of its stage tags. -/
theorem fold_growth (ss : List Stage) (r : LayerResult) :
    (ss.foldl advance r).rails.length≤r.rails.length+ss.length ∧
    (ss.foldl advance r).variableCount≤r.variableCount+15*ss.length*(r.rails.length+ss.length+1) ∧
    (ss.foldl advance r).instructions.length≤r.instructions.length+ss.length*(r.rails.length+ss.length+1) := by
  induction ss generalizing r with
  | nil => simp
  | cons s ss ih =>
    have h := ih (advance r s)
    have hr := s.render_rails_bound r.variableCount r.rails
    have hm := s.render_header_bound r.variableCount r.rails
    have hc := s.render_code_bound r.variableCount r.rails
    have hmul := Nat.mul_le_mul_left ss.length
      (show (s.render r.variableCount r.rails).rails.length+ss.length+1≤r.rails.length+(ss.length+1)+1 by omega)
    simp only [List.foldl_cons,List.length_cons,advance,LayerResult.then,List.length_append] at h ⊢
    refine ⟨by omega,?_,?_⟩ <;> nlinarith

end PlanarHom.PositiveBlockProgram
