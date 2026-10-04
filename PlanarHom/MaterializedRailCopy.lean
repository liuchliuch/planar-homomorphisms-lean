import PlanarHom.RoutingLayerValidity

/-! Full numerical materialization of the move-copy-restore routing macro. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open CountingCookLevin AdjacentRailRouting

def LayerResult.identity (m : ℕ) (rs : List ℕ) : LayerResult := ⟨m,rs,[]⟩
def LayerResult.then (r s : LayerResult) : LayerResult :=
  ⟨s.variableCount,s.rails,r.instructions++s.instructions⟩

theorem width_append (m : ℕ) (ops more : List Instruction) :
    width m (ops++more)=width (width m ops) more := by
  induction ops generalizing m with
  | nil => rfl
  | cons op ops ih => exact ih _

theorem valid_append (m : ℕ) (ops more : List Instruction) :
    Valid m (ops++more) ↔ Valid m ops ∧ Valid (width m ops) more := by
  induction ops generalizing m with
  | nil => simp [Valid,width]
  | cons op ops ih => simp only [List.cons_append,Valid,width,ih,and_assoc]

theorem LayerResult.WellFormed.then {m : ℕ} {r s : LayerResult}
    (hr : r.WellFormed m) (hs : s.WellFormed r.variableCount) : (r.then s).WellFormed m := by
  refine ⟨(valid_append m _ _).mpr ⟨hr.valid,?_⟩,?_,hs.rails_valid⟩
  · simpa [hr.width_eq] using hs.valid
  · change width m (r.instructions++s.instructions)=s.variableCount
    rw [width_append,hr.width_eq]
    exact hs.width_eq

theorem LayerResult.WellFormed.store_length {m : ℕ} {r : LayerResult}
    (hr : r.WellFormed m) (xs : List Bool) (hxs : xs.length=m) :
    (execute r.instructions xs).length=r.variableCount := by
  rw [execute_length,hxs,hr.width_eq]

def sweep (m : ℕ) (rs : List ℕ) : List ℕ → LayerResult
  | [] => .identity m rs
  | i::is =>
    let first := swapLayer m i rs
    first.then (sweep first.variableCount first.rails is)

theorem sweep_wellFormed (is : List ℕ) (m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (sweep m rs is).WellFormed m := by
  induction is generalizing m rs with
  | nil => exact ⟨trivial,rfl,hr⟩
  | cons i is ih =>
    have hfirst := swapLayer_wellFormed i m rs hr
    exact hfirst.then (ih _ _ hfirst.rails_valid)

@[simp] theorem sweep_accepts (is : List ℕ) (m : ℕ) (rs : List ℕ) (xs : List Bool) :
    Accepts (sweep m rs is).instructions xs := by
  induction is generalizing m rs xs with
  | nil => trivial
  | cons i is ih =>
    apply (accepts_append _ _ _).mpr
    exact ⟨swapLayer_accepts i m rs xs,ih _ _ _⟩

/-- Every numerical layer really implements the corresponding adjacent swap. -/
theorem sweep_values (is : List ℕ) (m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) :
    (sweep m rs is).rails.map (readBit (execute (sweep m rs is).instructions xs))=
      runSwaps is (rs.map (readBit xs)) := by
  induction is generalizing m rs xs with
  | nil => rfl
  | cons i is ih =>
    let first := swapLayer m i rs
    let ys := execute first.instructions xs
    have hf : first.WellFormed m := swapLayer_wellFormed i m rs hr
    have hys : ys.length=first.variableCount := hf.store_length xs hxs
    have ht := ih first.variableCount first.rails ys hys hf.rails_valid
    have hfirst : first.rails.map (readBit ys)=swapAt i (rs.map (readBit xs)) := by
      subst m
      exact swapLayer_values i rs xs hr
    rw [hfirst] at ht
    change (sweep first.variableCount first.rails is).rails.map
      (readBit (execute (first.instructions++(sweep first.variableCount first.rails is).instructions) xs))=_
    rw [execute_append]
    exact ht

/-- A requested occurrence is produced by literal swaps, a fanout layer, and
literal inverse swaps; all passive rails are materialized at every stage. -/
def copyMacro (originals index m : ℕ) (rs : List ℕ) : LayerResult :=
  if index<originals then
    let swaps := moveScript index (originals-1-index)
    let first := sweep m rs swaps
    let second := copyLayer first.variableCount (originals-1) first.rails
    let third := sweep second.variableCount second.rails swaps.reverse
    first.then (second.then third)
  else .identity m rs

theorem copyMacro_wellFormed (originals index m : ℕ) (rs : List ℕ) (hr : ∀x∈rs,x<m) :
    (copyMacro originals index m rs).WellFormed m := by
  unfold copyMacro
  split
  · have hfirst := sweep_wellFormed (moveScript index (originals-1-index)) m rs hr
    have hsecond := copyLayer_wellFormed (originals-1) _ _ hfirst.rails_valid
    have hthird := sweep_wellFormed (moveScript index (originals-1-index)).reverse _ _ hsecond.rails_valid
    exact hfirst.then (hsecond.then hthird)
  · exact ⟨trivial,rfl,hr⟩

@[simp] theorem copyMacro_accepts (originals index m : ℕ) (rs : List ℕ) (xs : List Bool) :
    Accepts (copyMacro originals index m rs).instructions xs := by
  unfold copyMacro
  split
  · apply (accepts_append _ _ _).mpr
    refine ⟨sweep_accepts _ _ _ _,?_⟩
    apply (accepts_append _ _ _).mpr
    exact ⟨copyLayer_accepts _ _ _ _,sweep_accepts _ _ _ _⟩
  · trivial

/-- The fully materialized macro has the same values as the proved logical one. -/
theorem copyMacro_values (originals index m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) :
    (copyMacro originals index m rs).rails.map
      (readBit (execute (copyMacro originals index m rs).instructions xs))=
      copyCircuit originals index (rs.map (readBit xs)) := by
  by_cases hi : index<originals
  · let swaps := moveScript index (originals-1-index)
    let first := sweep m rs swaps
    let second := copyLayer first.variableCount (originals-1) first.rails
    let third := sweep second.variableCount second.rails swaps.reverse
    let ys := execute first.instructions xs
    let zs := execute second.instructions ys
    have hf : first.WellFormed m := sweep_wellFormed swaps m rs hr
    have hs : second.WellFormed first.variableCount := copyLayer_wellFormed _ _ _ hf.rails_valid
    have hy : ys.length=first.variableCount := hf.store_length xs hxs
    have hz : zs.length=second.variableCount := hs.store_length ys hy
    have h1 : first.rails.map (readBit ys)=runSwaps swaps (rs.map (readBit xs)) :=
      sweep_values swaps m rs xs hxs hr
    have h2 : second.rails.map (readBit zs)=duplicateAt (originals-1) (first.rails.map (readBit ys)) := by
      simpa only [hy] using copyLayer_values (originals-1) first.rails ys (by simpa [hy] using hf.rails_valid)
    have h3 : third.rails.map (readBit (execute third.instructions zs))=
        runSwaps swaps.reverse (second.rails.map (readBit zs)) :=
      sweep_values swaps.reverse second.variableCount second.rails zs hz hs.rails_valid
    rw [h2,h1] at h3
    simp only [copyMacro,if_pos hi,LayerResult.then,copyCircuit]
    rw [execute_append,execute_append]
    exact h3
  · simp [copyMacro,copyCircuit,hi,LayerResult.identity,execute]

end PlanarHom.PositiveBlockProgram
