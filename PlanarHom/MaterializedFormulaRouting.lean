import PlanarHom.MaterializedClauseTermination

/-! Actual numeric clause-by-clause routing program, with every passive wire,
crossover, fanout, and clause occurrence explicitly materialized. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree CountingCookLevin AdjacentRailRouting

/-- Several requested occurrences, materialized consecutively. -/
def gatherMacro (n m : ℕ) (rs : List ℕ) : List ℕ → LayerResult
  | [] => .identity m rs
  | i::is =>
    let first := copyMacro n i m rs
    first.then (gatherMacro n first.variableCount first.rails is)

def copySequence (n : ℕ) (is : List ℕ) (xs : List Bool) : List Bool :=
  is.foldl (fun xs i => copyCircuit n i xs) xs

theorem gatherMacro_wellFormed (is : List ℕ) (n m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (gatherMacro n m rs is).WellFormed m := by
  induction is generalizing m rs with
  | nil => exact ⟨trivial,rfl,hr⟩
  | cons i is ih =>
    have hf := copyMacro_wellFormed n i m rs hr
    exact hf.then (ih _ _ hf.rails_valid)

@[simp] theorem gatherMacro_accepts (is : List ℕ) (n m : ℕ) (rs : List ℕ) (xs : List Bool) :
    Accepts (gatherMacro n m rs is).instructions xs := by
  induction is generalizing m rs xs with
  | nil => trivial
  | cons i is ih =>
    apply (accepts_append _ _ _).mpr
    exact ⟨copyMacro_accepts _ _ _ _ _,ih _ _ _⟩

theorem gatherMacro_values (is : List ℕ) (n m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) :
    (gatherMacro n m rs is).rails.map (readBit (execute (gatherMacro n m rs is).instructions xs))=
      copySequence n is (rs.map (readBit xs)) := by
  induction is generalizing m rs xs with
  | nil => rfl
  | cons i is ih =>
    let first := copyMacro n i m rs
    let ys := execute first.instructions xs
    have hf : first.WellFormed m := copyMacro_wellFormed n i m rs hr
    have hy : ys.length=first.variableCount := hf.store_length xs hxs
    have ht := ih first.variableCount first.rails ys hy hf.rails_valid
    have hfirst : first.rails.map (readBit ys)=copyCircuit n i (rs.map (readBit xs)) :=
      copyMacro_values n i m rs xs hxs hr
    rw [hfirst] at ht
    change (gatherMacro n first.variableCount first.rails is).rails.map
      (readBit (execute (first.instructions++(gatherMacro n first.variableCount first.rails is).instructions) xs))=_
    rw [execute_append]
    exact ht

def gatherClause (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) : LayerResult :=
  gatherMacro n m rs [c.1,c.2.1,c.2.2]

theorem gatherClause_wellFormed (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : ∀x∈rs,x<m) :
    (gatherClause n m rs c).WellFormed m := gatherMacro_wellFormed _ _ _ _ hr

theorem gatherClause_values (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) :
    (gatherClause n m rs c).rails.map (readBit (execute (gatherClause n m rs c).instructions xs))=
      PositiveFormulaRailRouting.gather n c (rs.map (readBit xs)) :=
  gatherMacro_values [c.1,c.2.1,c.2.2] n m rs xs hxs hr

theorem gatherClause_length (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : ∀x∈rs,x<m)
    (hlen : rs.length=n) (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    (gatherClause n m rs c).rails.length=n+3 := by
  let xs := List.replicate m false
  let bs := rs.map (readBit xs)
  have hb : bs.length=n := by simp [bs,hlen]
  have hg := gatherClause_values n m rs c xs (by simp [xs]) hr
  have hp := PositiveFormulaRailRouting.gather_correct bs [] c (by simpa [hb] using hc)
  simp only [List.append_nil,hb] at hp
  rw [hp] at hg
  have h := congrArg List.length hg
  simpa [hb] using h

def clauseLayer (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) : LayerResult :=
  let gathered := gatherClause n m rs c
  gathered.then (checkLayer n gathered.variableCount gathered.rails)

theorem clauseLayer_wellFormed (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : ∀x∈rs,x<m)
    (hlen : rs.length=n) (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    (clauseLayer n m rs c).WellFormed m := by
  have hg := gatherClause_wellFormed n m rs c hr
  exact hg.then (checkLayer_wellFormed n _ _ hg.rails_valid (gatherClause_length n m rs c hr hlen hc))

theorem clauseLayer_length (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : ∀x∈rs,x<m)
    (hlen : rs.length=n) (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    (clauseLayer n m rs c).rails.length=n := by
  simp only [clauseLayer,LayerResult.then,checkLayer,wireRails_length,List.length_take,
    gatherClause_length n m rs c hr hlen hc]
  omega

theorem clauseLayer_values (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) (hlen : rs.length=n)
    (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    (clauseLayer n m rs c).rails.map (readBit (execute (clauseLayer n m rs c).instructions xs))=
      rs.map (readBit xs) := by
  let gathered := gatherClause n m rs c
  let ys := execute gathered.instructions xs
  have hg : gathered.WellFormed m := gatherClause_wellFormed n m rs c hr
  have hy := hg.store_length xs hxs
  have hcheck := checkLayer_values n gathered.variableCount gathered.rails ys hy hg.rails_valid
  have hvals := gatherClause_values n m rs c xs hxs hr
  have hb : (rs.map (readBit xs)).length=n := by simp [hlen]
  have hp := PositiveFormulaRailRouting.gather_correct (rs.map (readBit xs)) [] c (by simpa [hb] using hc)
  simp only [List.append_nil,hb] at hp
  rw [hvals,hp] at hcheck
  change (checkLayer n gathered.variableCount gathered.rails).rails.map
    (readBit (execute (gathered.instructions++(checkLayer n gathered.variableCount gathered.rails).instructions) xs))=_
  rw [execute_append,hcheck]
  rw [List.take_append_of_le_length hb.ge,List.take_of_length_le hb.le]

theorem clauseLayer_accepts (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) (hlen : rs.length=n)
    (hc : c.1<n ∧ c.2.1<n ∧ c.2.2<n) :
    Accepts (clauseLayer n m rs c).instructions xs ↔
      ExactlyOne (readBit (rs.map (readBit xs)) c.1) (readBit (rs.map (readBit xs)) c.2.1)
        (readBit (rs.map (readBit xs)) c.2.2) := by
  let gathered := gatherClause n m rs c
  let ys := execute gathered.instructions xs
  have hg : gathered.WellFormed m := gatherClause_wellFormed n m rs c hr
  have hy := hg.store_length xs hxs
  have hl := gatherClause_length n m rs c hr hlen hc
  have hcheck := checkLayer_accepts n gathered.variableCount gathered.rails ys hy hg.rails_valid hl
  have hvals := gatherClause_values n m rs c xs hxs hr
  let bs := rs.map (readBit xs)
  have hb : bs.length=n := by simp [bs,hlen]
  have hbc : c.1<bs.length ∧ c.2.1<bs.length ∧ c.2.2<bs.length := by simpa [hb] using hc
  have hp := PositiveFormulaRailRouting.gather_correct bs [] c hbc
  simp only [List.append_nil,hb] at hp
  rw [hvals,hp] at hcheck
  change Accepts (gathered.instructions++(checkLayer n gathered.variableCount gathered.rails).instructions) xs ↔ _
  rw [accepts_append]
  have hgaccept : Accepts gathered.instructions xs := gatherMacro_accepts _ _ _ _ _
  simp only [hgaccept,true_and]
  rw [hcheck]
  change ExactlyOne (readBit (bs++[bs[c.2.2],bs[c.2.1],bs[c.1]]) n)
    (readBit (bs++[bs[c.2.2],bs[c.2.1],bs[c.1]]) (n+1))
    (readBit (bs++[bs[c.2.2],bs[c.2.1],bs[c.1]]) (n+2)) ↔
    ExactlyOne (readBit bs c.1) (readBit bs c.2.1) (readBit bs c.2.2)
  simp only [readBit,List.getElem?_append_right (by omega : bs.length≤n),List.getElem?_append_right (by omega : bs.length≤n+1),
    List.getElem?_append_right (by omega : bs.length≤n+2),hb,Nat.sub_self,Nat.add_sub_cancel_left]
  simp only [List.getElem?_cons_zero,List.getElem?_cons_succ,Option.getD_some,
    List.getElem?_eq_getElem hbc.1,List.getElem?_eq_getElem hbc.2.1,List.getElem?_eq_getElem hbc.2.2]
  unfold ExactlyOne
  omega

end PlanarHom.PositiveBlockProgram
