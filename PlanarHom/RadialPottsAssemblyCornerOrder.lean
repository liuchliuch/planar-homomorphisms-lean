import PlanarHom.RadialPottsAssemblyCircleArches

/-! Actual circle routing for k nested wires in every gap of a cyclic row.
The noninterleaving inequalities are derived for every row size, including a
single dart and empty lane sets; they are not required as drawing premises. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph PlanarityLRRealization
namespace CornerOrder

def next {n : ℕ} (j : Fin n) : Fin n :=
  if h : j.val+1<n then ⟨j.val+1,h⟩ else ⟨0,by omega⟩

def graph (n k : ℕ) : MultiGraph (Fin n × Fin (2*k)) (Fin n × Fin k) where
  src e := (e.1,⟨k+e.2.val,by omega⟩)
  dst e := (next e.1,⟨k-1-e.2.val,by omega⟩)

def rank {n k : ℕ} (v : Fin n × Fin (2*k)) : ℕ := v.2.val+2*k*v.1.val

theorem rank_injective {n k : ℕ} : Function.Injective (@rank n k) := by
  intro u v h
  apply finProdFinEquiv.injective
  apply Fin.ext
  exact h

def lo {n k : ℕ} (e : Fin n × Fin k) : ℕ :=
  if e.1.val+1<n then 2*k*e.1.val+k+e.2.val else k-1-e.2.val

def hi {n k : ℕ} (e : Fin n × Fin k) : ℕ :=
  if e.1.val+1<n then 2*k*(e.1.val+1)+(k-1-e.2.val) else 2*k*e.1.val+k+e.2.val

theorem lo_lt_hi {n k : ℕ} (e : Fin n × Fin k) : lo e<hi e := by
  have ha := e.2.isLt
  unfold lo hi
  split_ifs <;> (try simp only [Nat.mul_add,Nat.mul_one]) <;> omega

theorem rank_endpoints {n k : ℕ} (e : Fin n × Fin k) :
    (rank ((graph n k).src e)=lo e ∧ rank ((graph n k).dst e)=hi e) ∨
    (rank ((graph n k).src e)=hi e ∧ rank ((graph n k).dst e)=lo e) := by
  by_cases h : e.1.val+1<n
  · left
    simp [graph,rank,lo,hi,next,h,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  · right
    simp [graph,rank,lo,hi,next,h,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]

private theorem noninterleaving_nat {n k : ℕ} (e f : Fin n × Fin k) (hef : e≠f) :
    hi e<lo f ∨ hi f<lo e ∨ (lo e<lo f ∧ hi f<hi e) ∨ (lo f<lo e ∧ hi e<hi f) := by
  have ha := e.2.isLt
  have hb := f.2.isLt
  have hj := e.1.isLt
  have hl := f.1.isLt
  have hnot : e.1.val≠f.1.val ∨ e.2.val≠f.2.val := by
    by_contra h
    push_neg at h
    exact hef (Prod.ext (Fin.ext h.1) (Fin.ext h.2))
  have hmul : ∀ i j : ℕ,i<j→2*k*i+2*k≤2*k*j := by
    intro i j hij
    have h := Nat.mul_le_mul_left (2*k) (show i+1≤j by omega)
    simpa only [Nat.mul_add,Nat.mul_one] using h
  have hew : e.1.val+1<n ∨ e.1.val+1=n := by omega
  have hfw : f.1.val+1<n ∨ f.1.val+1=n := by omega
  unfold lo hi
  split_ifs with he hf
  all_goals
    try simp only [Nat.mul_add,Nat.mul_one]
    rcases lt_trichotomy e.1.val f.1.val with h | h | h
    · have hm := hmul _ _ h
      omega
    · simp only [h] at *
      omega
    · have hm := hmul _ _ h
      omega

/-- Any strictly increasing real heights retain the actual gap matching. -/
theorem noninterleaving {n k : ℕ} (height : ℕ → ℝ) (hmono : StrictMono height)
    (e f : Fin n × Fin k) (hef : e≠f) :
    Noninterleaving (height (lo e)) (height (hi e)) (height (lo f)) (height (hi f)) := by
  rcases noninterleaving_nat e f hef with h | h | h | h
  · exact Or.inl (hmono h)
  · exact Or.inr (Or.inl (hmono h))
  · exact Or.inr (Or.inr (Or.inl ⟨hmono h.1,hmono h.2⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hmono h.1,hmono h.2⟩))

def drawing (n k : ℕ) (height : ℕ → ℝ) (hmono : StrictMono height) :
    PlaneDrawing (graph n k) := by
  apply circleDrawing (graph n k) (fun v => height (rank v)) (hmono.injective.comp rank_injective)
  · intro e h
    have hv := congrArg (fun v : Fin n × Fin (2*k) => v.2.val) h
    change k+e.2.val=k-1-e.2.val at hv
    have ha := e.2.isLt
    omega
  · intro e f hef
    have hh := noninterleaving height hmono e f hef
    have he := hmono (lo_lt_hi e)
    have hf := hmono (lo_lt_hi f)
    rcases rank_endpoints e with he' | he' <;>
      rcases rank_endpoints f with hf' | hf' <;>
      simp only [he'.1,he'.2,hf'.1,hf'.2,min_eq_left he.le,max_eq_right he.le,
        min_eq_left hf.le,max_eq_right hf.le,min_eq_right he.le,max_eq_left he.le,
        min_eq_right hf.le,max_eq_left hf.le] <;> exact hh

/-- Clockwise order uses decreasing chart heights, covering the orientation
of the actual computed rotation without reflecting the ambient drawing. -/
theorem noninterleaving_anti {n k : ℕ} (height : ℕ → ℝ) (hmono : StrictAnti height)
    (e f : Fin n × Fin k) (hef : e≠f) :
    Noninterleaving (height (hi e)) (height (lo e)) (height (hi f)) (height (lo f)) := by
  rcases noninterleaving_nat e f hef with h | h | h | h
  · exact Or.inr (Or.inl (hmono h))
  · exact Or.inl (hmono h)
  · exact Or.inr (Or.inr (Or.inl ⟨hmono h.2,hmono h.1⟩))
  · exact Or.inr (Or.inr (Or.inr ⟨hmono h.2,hmono h.1⟩))

def clockwiseDrawing (n k : ℕ) (height : ℕ → ℝ) (hmono : StrictAnti height) :
    PlaneDrawing (graph n k) := by
  apply circleDrawing (graph n k) (fun v => height (rank v)) (hmono.injective.comp rank_injective)
  · intro e h
    have hv := congrArg (fun v : Fin n × Fin (2*k) => v.2.val) h
    change k+e.2.val=k-1-e.2.val at hv
    have ha := e.2.isLt
    omega
  · intro e f hef
    have hh := noninterleaving_anti height hmono e f hef
    have he := hmono (lo_lt_hi e)
    have hf := hmono (lo_lt_hi f)
    rcases rank_endpoints e with he' | he' <;>
      rcases rank_endpoints f with hf' | hf' <;>
      simp only [he'.1,he'.2,hf'.1,hf'.2,min_eq_left he.le,max_eq_right he.le,
        min_eq_left hf.le,max_eq_right hf.le,min_eq_right he.le,max_eq_left he.le,
        min_eq_right hf.le,max_eq_left hf.le] <;> exact hh

end CornerOrder
end PlanarHom.RadialPottsAssemblyGeometry
