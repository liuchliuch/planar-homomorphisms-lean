import PlanarHom.RoutingCellTrace

/-! Distinct materialized boundary ports, including repeated source literals. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree

theorem wireRails_nodup (m : ℕ) (rs : List ℕ) : (wireRails m rs).Nodup := by
  induction rs generalizing m with
  | nil => simp [wireRails]
  | cons a rs ih =>
    apply List.nodup_cons.mpr
    refine ⟨?_,ih (m+6)⟩
    intro hm
    have h := (wireRails_bounds (m+6) rs m hm).1
    omega

theorem swapLayer_lower (i m : ℕ) (rs : List ℕ) (x : ℕ) (hx : x∈(swapLayer m i rs).rails) : m≤x := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [swapLayer,passive,wireRails] at hx
    | cons a rs =>
      cases rs with
      | nil => exact (wireRails_bounds m [a] x hx).1
      | cons b rs =>
        change x∈m::(m+1)::wireRails (m+15) rs at hx
        simp only [List.mem_cons] at hx
        rcases hx with h | h | h
        · omega
        · omega
        · have hb := (wireRails_bounds (m+15) rs x h).1; omega
  | succ i ih =>
    cases rs with
    | nil => simp [swapLayer,passive,wireRails] at hx
    | cons a rs =>
      change x∈m::(swapLayer (m+6) i rs).rails at hx
      rcases List.mem_cons.mp hx with h | h
      · omega
      · have hh := ih (m+6) rs h; omega

theorem copyLayer_lower (i m : ℕ) (rs : List ℕ) (x : ℕ) (hx : x∈(copyLayer m i rs).rails) : m≤x := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [copyLayer,passive,wireRails] at hx
    | cons a rs =>
      change x∈(m+1)::m::wireRails (m+12) rs at hx
      simp only [List.mem_cons] at hx
      rcases hx with h | h | h
      · omega
      · omega
      · have hb := (wireRails_bounds (m+12) rs x h).1; omega
  | succ i ih =>
    cases rs with
    | nil => simp [copyLayer,passive,wireRails] at hx
    | cons a rs =>
      change x∈m::(copyLayer (m+6) i rs).rails at hx
      rcases List.mem_cons.mp hx with h | h
      · omega
      · have hh := ih (m+6) rs h; omega

theorem swapLayer_nodup (i m : ℕ) (rs : List ℕ) : (swapLayer m i rs).rails.Nodup := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [swapLayer,passive,wireRails]
    | cons a rs =>
      cases rs with
      | nil => exact wireRails_nodup m [a]
      | cons b rs =>
        change (m::(m+1)::wireRails (m+15) rs).Nodup
        have h0 : m∉wireRails (m+15) rs := fun h => by have hh := (wireRails_bounds _ _ _ h).1; omega
        have h1 : m+1∉wireRails (m+15) rs := fun h => by have hh := (wireRails_bounds _ _ _ h).1; omega
        simp [h0,h1,wireRails_nodup]
  | succ i ih =>
    cases rs with
    | nil => simp [swapLayer,passive,wireRails]
    | cons a rs =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih (m+6) rs⟩
      intro h
      have hh := swapLayer_lower i (m+6) rs m h
      omega

theorem copyLayer_nodup (i m : ℕ) (rs : List ℕ) : (copyLayer m i rs).rails.Nodup := by
  induction i generalizing m rs with
  | zero =>
    cases rs with
    | nil => simp [copyLayer,passive,wireRails]
    | cons a rs =>
      change ((m+1)::m::wireRails (m+12) rs).Nodup
      have h0 : m∉wireRails (m+12) rs := fun h => by have hh := (wireRails_bounds _ _ _ h).1; omega
      have h1 : m+1∉wireRails (m+12) rs := fun h => by have hh := (wireRails_bounds _ _ _ h).1; omega
      simp [h0,h1,wireRails_nodup]
  | succ i ih =>
    cases rs with
    | nil => simp [copyLayer,passive,wireRails]
    | cons a rs =>
      apply List.nodup_cons.mpr
      refine ⟨?_,ih (m+6) rs⟩
      intro h
      have hh := copyLayer_lower i (m+6) rs m h
      omega

theorem sweep_nodup (is : List ℕ) (m : ℕ) (rs : List ℕ) (hr : rs.Nodup) :
    (sweep m rs is).rails.Nodup := by
  induction is generalizing m rs with
  | nil => exact hr
  | cons i is ih => exact ih _ _ (swapLayer_nodup i m rs)

theorem copyMacro_nodup (n i m : ℕ) (rs : List ℕ) (hr : rs.Nodup) :
    (copyMacro n i m rs).rails.Nodup := by
  unfold copyMacro
  split
  · exact sweep_nodup _ _ _ (copyLayer_nodup _ _ _)
  · exact hr

theorem gatherMacro_nodup (is : List ℕ) (n m : ℕ) (rs : List ℕ) (hr : rs.Nodup) :
    (gatherMacro n m rs is).rails.Nodup := by
  induction is generalizing m rs with
  | nil => exact hr
  | cons i is ih => exact ih _ _ (copyMacro_nodup n i m rs hr)

theorem gatherClause_nodup (n m : ℕ) (rs : List ℕ) (c : Clause ℕ) (hr : rs.Nodup) :
    (gatherClause n m rs c).rails.Nodup := gatherMacro_nodup _ _ _ _ hr

/-- Original repeated literals still terminate at three distinct actual rails. -/
theorem clause_occurrences_nodup (n m : ℕ) (rs : List ℕ) (c : Clause ℕ)
    (hr : rs.Nodup) : (gatherClause n m rs c).rails.Nodup := gatherClause_nodup n m rs c hr

end PlanarHom.PositiveBlockProgram
