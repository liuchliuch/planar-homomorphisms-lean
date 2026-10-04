import PlanarHom.RadialPottsOnionBoundaryPaths

/-! NEW reconstruction: the red onion has exactly the two stated lane-indexed
path families. Every white vertex reaches a boundary port, so no unobserved
closed component is hidden inside the tile. -/
noncomputable section
open Classical
namespace PlanarHom.RadialPottsTile.OnionBoundary
open MultiGraph

def canonicalPort {k : ℕ} (p : Component k) : Vertex k :=
  .inr (⟨2*p.1.val,by have := p.1.isLt; omega⟩,p.2)

theorem red_reach_component {k : ℕ} {u v : Vertex k} (h : RedReach u v) : component u=component v := by
  induction h with
  | rel u v h =>
    obtain ⟨e,_,rfl,rfl⟩ := h
    cases e with
    | inl e => exact component_long e
    | inr e => exact component_red e
  | refl => rfl
  | symm _ _ _ ih => exact ih.symm
  | trans _ _ _ _ _ ih ij => exact ih.trans ij

@[simp] theorem component_canonicalPort {k : ℕ} (p : Component k) : component (canonicalPort p)=p := by
  apply Prod.ext <;> apply Fin.ext
  · dsimp [canonicalPort,component]
    omega
  · simp [canonicalPort,component]

theorem port_to_canonical {k : ℕ} (s : Fin 4) (a : Fin k) :
    RedReach (.inr (s,a)) (canonicalPort (component (.inr (s,a)))) := by
  let c : Fin 2 := ⟨s.val/2,by have := s.isLt; omega⟩
  by_cases hp : s.val%2=0
  · have hs : (⟨2*c.val,by have := c.isLt; omega⟩ : Fin 4)=s := by
      apply Fin.ext
      dsimp [c]
      omega
    have he : canonicalPort (component (.inr (s,a)))=.inr (s,a) := by
      simp only [canonicalPort,component,if_pos hp]
      exact congrArg (fun t : Fin 4 => Sum.inr (t,a)) hs
    rw [he]
  · let b : Fin k := ⟨k-1-a.val,by have := a.isLt; omega⟩
    have h := red_port_pair c b
    have hr : (⟨2*c.val+1,by have := c.isLt; omega⟩,
        (⟨k-1-b.val,by have := b.isLt; omega⟩ : Fin k))=(s,a) := by
      apply Prod.ext <;> apply Fin.ext
      · dsimp [c]
        have := s.isLt
        omega
      · dsimp [b]
        have := a.isLt
        omega
    rw [hr] at h
    have hl : canonicalPort (component (.inr (s,a)))=.inr (⟨2*c.val,by have := c.isLt; omega⟩,b) := by
      simp [canonicalPort,component,hp,c,b]
    rw [hl]
    exact Relation.EqvGen.symm _ _ h

private theorem whiteAt_reaches_port {k : ℕ} (r : Fin k) (s : Fin 4) (t : ℕ) (ht : t≤2*r.val) :
    ∃ p : Port k,RedReach (.inl (whiteAt r s t ht)) (.inr p) := by
  rcases Nat.mod_two_eq_zero_or_one t with heven | hodd
  · let a := t/2
    have ha : a≤r.val := by dsimp [a]; omega
    have he : whiteAt r s t ht=whiteAt r s (2*a) (by omega) := by
      apply whiteAt_ext <;> dsimp [a] <;> omega
    refine ⟨(s,outerLane r s a ha),?_⟩
    rw [he]
    exact evenOffset_to_port r s a ha
  · by_cases hs : s.val%2=0
    · let a := (t-1)/2
      have ha : a≤r.val := by dsimp [a]; omega
      have hstep := reach_red_inner r s (t-1) (by omega) (by omega)
      have he : whiteAt r s (t-1+1) (by omega)=whiteAt r s t ht := by apply whiteAt_ext <;> omega
      have hf : whiteAt r s (t-1) (by omega)=whiteAt r s (2*a) (by omega) := by
        apply whiteAt_ext <;> dsimp [a] <;> omega
      rw [he,hf] at hstep
      exact ⟨(s,outerLane r s a ha),Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ hstep) (evenOffset_to_port r s a ha)⟩
    · let a := (t+1)/2
      have ha : a≤r.val := by dsimp [a]; omega
      have hstep := reach_red_inner r s t (by omega) (by omega)
      have he : whiteAt r s (t+1) (by omega)=whiteAt r s (2*a) (by omega) := by
        apply whiteAt_ext <;> dsimp [a] <;> omega
      rw [he] at hstep
      exact ⟨(s,outerLane r s a ha),Relation.EqvGen.trans _ _ _ hstep (evenOffset_to_port r s a ha)⟩

/-- Every actual vertex reaches the canonical even-side port of its label. -/
theorem red_vertex_to_canonical {k : ℕ} (v : Vertex k) : RedReach v (canonicalPort (component v)) := by
  cases v with
  | inr p => exact port_to_canonical p.1 p.2
  | inl w =>
    obtain ⟨p,hp⟩ := whiteAt_reaches_port w.1 (side w) (offset w) (offset_le w)
    rw [whiteAt_side_offset] at hp
    have hc := red_reach_component hp
    rw [hc]
    exact Relation.EqvGen.trans _ _ _ hp (port_to_canonical p.1 p.2)

/-- Exact component characterization, including all inner white vertices. -/
theorem red_connected_iff {k : ℕ} (u v : Vertex k) : RedReach u v ↔ component u=component v := by
  constructor
  · exact red_reach_component
  · intro h
    have hu := red_vertex_to_canonical u
    have hv := red_vertex_to_canonical v
    rw [h] at hu
    exact Relation.EqvGen.trans _ _ _ hu (Relation.EqvGen.symm _ _ hv)

noncomputable def redComponentEquiv (k : ℕ) : (redGraph k).Components Finset.univ ≃ Component k where
  toFun := Quotient.lift component (fun _ _ h => red_reach_component h)
  invFun p := Quotient.mk _ (canonicalPort p)
  left_inv q := by
    induction q using Quotient.inductionOn with
    | h v =>
      apply Quotient.sound
      exact Relation.EqvGen.symm _ _ (red_vertex_to_canonical v)
  right_inv p := component_canonicalPort p

theorem red_componentCount (k : ℕ) : (redGraph k).componentCount Finset.univ=2*k := by
  rw [componentCount,Fintype.card_congr (redComponentEquiv k)]
  simp [Component]
end PlanarHom.RadialPottsTile.OnionBoundary
