import PlanarHom.RadialPottsTile
import Mathlib.Tactic.FinCases

/-! An explicit vertex atlas for the unswitched red onion. The atlas is purely
literal: its coordinates record the two terminal-to-terminal path families. -/
namespace PlanarHom.RadialPottsTile.OnionBoundary

abbrev Component (k : ℕ) := Fin 2 × Fin k
abbrev Atlas (k : ℕ) := (p : Component k) × Fin (4*(k-p.2.val))

/-- White vertex in side-local coordinates on a ring. -/
def whiteAt {k : ℕ} (r : Fin k) (s : Fin 4) (t : ℕ)
    (ht : t ≤ 2*r.val) : White k :=
  ⟨r,⟨s.val*(2*r.val+1)+t,by
    have hs := s.isLt
    have hh := Nat.mul_le_mul_right (2*r.val+1) (show s.val ≤ 3 by omega)
    omega⟩⟩

def side {k : ℕ} (w : White k) : Fin 4 :=
  ⟨w.2.val/(2*w.1.val+1),by
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    have := w.2.isLt
    omega⟩

def offset {k : ℕ} (w : White k) : ℕ := w.2.val%(2*w.1.val+1)

theorem offset_le {k : ℕ} (w : White k) : offset w ≤ 2*w.1.val := by
  have := Nat.mod_lt w.2.val (show 0<2*w.1.val+1 by omega)
  unfold offset
  omega

/-- The component label given by the inverse side-coordinate formulas. -/
def component {k : ℕ} : Vertex k → Component k
  | .inl w => (⟨(side w).val/2,by have := (side w).isLt; omega⟩,
      if (side w).val%2=0 then
        ⟨offset w/2,by have := offset_le w; have := w.1.isLt; omega⟩
      else ⟨w.1.val-(offset w+1)/2,by have := w.1.isLt; omega⟩)
  | .inr p => (⟨p.1.val/2,by have := p.1.isLt; omega⟩,
      if p.1.val%2=0 then p.2 else ⟨k-1-p.2.val,by have := p.2.isLt; omega⟩)

/-- Visit the initial port, descend the even side, ascend the odd side, and
visit the terminal port. There are exactly `4*(k-a)` vertices on this path. -/
def pathVertex {k : ℕ} (c : Fin 2) (a : Fin k)
    (j : Fin (4*(k-a.val))) : Vertex k :=
  if h₀ : j.val=0 then
    .inr (⟨2*c.val,by have := c.isLt; omega⟩,a)
  else if h₁ : j.val<2*(k-a.val) then
    .inl (whiteAt ⟨k-1-(j.val-1)/2,by have := a.isLt; omega⟩
      ⟨2*c.val,by have := c.isLt; omega⟩ (2*a.val+(j.val-1)%2) (by
        have := a.isLt
        have := Nat.mod_lt (j.val-1) (by omega : 0<2)
        dsimp
        omega))
  else if h₂ : j.val<4*(k-a.val)-1 then
    .inl (whiteAt ⟨a.val+(j.val-2*(k-a.val)+1)/2,by have := a.isLt; omega⟩
      ⟨2*c.val+1,by have := c.isLt; omega⟩ (j.val-2*(k-a.val)) (by dsimp; omega))
  else .inr (⟨2*c.val+1,by have := c.isLt; omega⟩,
    ⟨k-a.val-1,by have := a.isLt; omega⟩)

def atlasVertex {k : ℕ} (z : Atlas k) : Vertex k :=
  pathVertex z.1.1 z.1.2 z.2


@[simp] theorem side_whiteAt {k : ℕ} (r : Fin k) (s : Fin 4) (t : ℕ)
    (ht : t ≤ 2*r.val) : side (whiteAt r s t ht)=s := by
  apply Fin.ext
  dsimp [side,whiteAt]
  rw [Nat.mul_comm s.val, Nat.mul_add_div (by omega : 0<2*r.val+1),
    Nat.div_eq_of_lt (by omega : t<2*r.val+1)]
  omega

@[simp] theorem offset_whiteAt {k : ℕ} (r : Fin k) (s : Fin 4) (t : ℕ)
    (ht : t ≤ 2*r.val) : offset (whiteAt r s t ht)=t := by
  dsimp [offset,whiteAt]
  rw [Nat.mul_comm s.val, Nat.mul_add_mod,Nat.mod_eq_of_lt (by omega : t<2*r.val+1)]

@[simp] theorem whiteAt_side_offset {k : ℕ} (w : White k) :
    whiteAt w.1 (side w) (offset w) (offset_le w)=w := by
  apply white_ext
  · rfl
  · dsimp [whiteAt,side,offset]
    simpa only [Nat.mul_comm] using Nat.div_add_mod w.2.val (2*w.1.val+1)

/-- Extensionality without having to align the dependent index proofs. -/
theorem whiteAt_ext {k : ℕ} (r r' : Fin k) (s s' : Fin 4)
    (t t' : ℕ) (ht : t ≤ 2*r.val) (ht' : t' ≤ 2*r'.val)
    (hr : r.val=r'.val) (hs : s.val=s'.val) (htt : t=t') :
    whiteAt r s t ht=whiteAt r' s' t' ht' := by
  apply white_ext
  · exact hr
  · dsimp [whiteAt]
    rw [hr,hs,htt]


theorem pathVertex_surjective_white {k : ℕ} (r : Fin k) (s : Fin 4)
    (t : ℕ) (ht : t ≤ 2*r.val) :
    ∃ z : Atlas k, atlasVertex z=.inl (whiteAt r s t ht) := by
  let c : Fin 2 := ⟨s.val/2,by have := s.isLt; omega⟩
  by_cases he : s.val%2=0
  · let a : Fin k := ⟨t/2,by have := r.isLt; omega⟩
    let j : Fin (4*(k-a.val)) :=
      ⟨2*(k-r.val-1)+1+t%2,by dsimp [a]; have := r.isLt; omega⟩
    refine ⟨⟨(c,a),j⟩,?_⟩
    have h₀ : j.val≠0 := by dsimp [j]; omega
    have h₁ : j.val<2*(k-a.val) := by dsimp [j,a]; have := r.isLt; omega
    dsimp [atlasVertex]
    rw [pathVertex,dif_neg h₀,dif_pos h₁]
    apply congrArg Sum.inl
    apply whiteAt_ext
    · dsimp [j]
      have := r.isLt
      omega
    · dsimp [c]
      omega
    · dsimp [j,a]
      omega
  · let a : Fin k := ⟨r.val-(t+1)/2,by have := r.isLt; omega⟩
    let j : Fin (4*(k-a.val)) :=
      ⟨2*(k-a.val)+t,by dsimp [a]; have := r.isLt; omega⟩
    refine ⟨⟨(c,a),j⟩,?_⟩
    have h₀ : j.val≠0 := by dsimp [j]; have := a.isLt; omega
    have h₁ : ¬j.val<2*(k-a.val) := by dsimp [j]; omega
    have h₂ : j.val<4*(k-a.val)-1 := by dsimp [j,a]; have := r.isLt; omega
    dsimp [atlasVertex]
    rw [pathVertex,dif_neg h₀,dif_neg h₁,dif_pos h₂]
    apply congrArg Sum.inl
    apply whiteAt_ext
    · dsimp [j,a]
      omega
    · dsimp [c]
      omega
    · dsimp [j]
      omega

theorem atlasVertex_surjective {k : ℕ} : Function.Surjective (@atlasVertex k) := by
  intro v
  cases v with
  | inl w =>
    simpa only [whiteAt_side_offset] using
      pathVertex_surjective_white w.1 (side w) (offset w) (offset_le w)
  | inr p =>
    let c : Fin 2 := ⟨p.1.val/2,by have := p.1.isLt; omega⟩
    by_cases he : p.1.val%2=0
    · let j : Fin (4*(k-p.2.val)) := ⟨0,by have := p.2.isLt; omega⟩
      refine ⟨⟨(c,p.2),j⟩,?_⟩
      dsimp [atlasVertex]
      rw [pathVertex,dif_pos (show j.val=0 by rfl)]
      apply congrArg Sum.inr
      apply Prod.ext
      · apply Fin.ext
        dsimp [c]
        omega
      · rfl
    · let a : Fin k := ⟨k-1-p.2.val,by have := p.2.isLt; omega⟩
      let j : Fin (4*(k-a.val)) := ⟨4*(k-a.val)-1,by have := a.isLt; omega⟩
      refine ⟨⟨(c,a),j⟩,?_⟩
      have h₀ : j.val≠0 := by dsimp [j]; have := a.isLt; omega
      have h₁ : ¬j.val<2*(k-a.val) := by dsimp [j]; have := a.isLt; omega
      have h₂ : ¬j.val<4*(k-a.val)-1 := by dsimp [j]; omega
      dsimp [atlasVertex]
      rw [pathVertex,dif_neg h₀,dif_neg h₁,dif_neg h₂]
      apply congrArg Sum.inr
      apply Prod.ext <;> apply Fin.ext
      · dsimp [c]
        omega
      · dsimp [a]
        have := p.2.isLt
        omega


open scoped BigOperators

theorem card_atlas (k : ℕ) : Fintype.card (Atlas k)=4*k^2+4*k := by
  have hsum : (∑ a : Fin k, 4*(k-a.val))=2*k*(k+1) := by
    rw [← Equiv.sum_comp (Fin.revPerm : Fin k ≃ Fin k)]
    have hfun : (fun a : Fin k => 4*(k-(Fin.revPerm a).val))=
        (fun a : Fin k => 4*(a.val+1)) := by
      funext a
      have := a.isLt
      dsimp [Fin.revPerm,Fin.rev]
      omega
    rw [hfun,Fin.sum_univ_eq_sum_range (fun a => 4*(a+1)) k]
    change (∑ a ∈ Finset.range k, 4*(a+1))=2*k*(k+1)
    clear hfun
    induction k with
    | zero => simp
    | succ k ih => rw [Finset.sum_range_succ,ih]; ring
  simp only [Atlas,Fintype.card_sigma,Fintype.card_fin,Component,
    Fintype.sum_prod_type]
  simp only [hsum,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem atlasVertex_bijective (k : ℕ) : Function.Bijective (@atlasVertex k) := by
  apply (Fintype.bijective_iff_surjective_and_card _).mpr
  exact ⟨atlasVertex_surjective,by rw [card_atlas,card_vertex]⟩

noncomputable def atlasEquiv (k : ℕ) : Atlas k ≃ Vertex k :=
  Equiv.ofBijective _ (atlasVertex_bijective k)


@[simp] theorem component_pathVertex {k : ℕ} (c : Fin 2) (a : Fin k)
    (j : Fin (4*(k-a.val))) : component (pathVertex c a j)=(c,a) := by
  have ha := a.isLt
  by_cases h₀ : j.val=0
  · rw [pathVertex,dif_pos h₀]
    simp only [component,Nat.mul_mod_right,ite_true]
    apply Prod.ext
    · apply Fin.ext
      dsimp
      omega
    · rfl
  · by_cases h₁ : j.val<2*(k-a.val)
    · rw [pathVertex,dif_neg h₀,dif_pos h₁]
      simp only [component,side_whiteAt,offset_whiteAt,Nat.mul_mod_right,ite_true]
      apply Prod.ext <;> apply Fin.ext <;> dsimp [whiteAt]
      · omega
      · omega
    · by_cases h₂ : j.val<4*(k-a.val)-1
      · rw [pathVertex,dif_neg h₀,dif_neg h₁,dif_pos h₂]
        simp only [component,side_whiteAt,offset_whiteAt]
        have hp : (2*c.val+1)%2≠0 := by omega
        rw [if_neg hp]
        apply Prod.ext <;> apply Fin.ext <;> dsimp [whiteAt]
        · omega
        · omega
      · rw [pathVertex,dif_neg h₀,dif_neg h₁,dif_neg h₂]
        simp only [component]
        have hp : (2*c.val+1)%2≠0 := by omega
        rw [if_neg hp]
        apply Prod.ext <;> apply Fin.ext <;> dsimp [whiteAt]
        · omega
        · omega

@[simp] theorem component_atlasVertex {k : ℕ} (z : Atlas k) :
    component (atlasVertex z)=z.1 := component_pathVertex z.1.1 z.1.2 z.2

@[simp] theorem atlasEquiv_apply {k : ℕ} (z : Atlas k) :
    atlasEquiv k z=atlasVertex z := rfl

@[simp] theorem atlasEquiv_symm_component {k : ℕ} (v : Vertex k) :
    ((atlasEquiv k).symm v).1=component v := by
  simpa only [← atlasEquiv_apply,Equiv.apply_symm_apply] using
    (component_atlasVertex ((atlasEquiv k).symm v)).symm

/-- The inverse path position, indexed by the literal component label. -/
noncomputable def position {k : ℕ} (v : Vertex k) :
    Fin (4*(k-(component v).2.val)) :=
  Fin.cast (congrArg (fun p : Component k => 4*(k-p.2.val))
    (atlasEquiv_symm_component v)) ((atlasEquiv k).symm v).2


theorem atlasEquiv_symm_eq {k : ℕ} (v : Vertex k) :
    (atlasEquiv k).symm v=⟨component v,position v⟩ := by
  apply Sigma.ext (atlasEquiv_symm_component v)
  apply (Fin.heq_ext_iff (congrArg (fun p : Component k => 4*(k-p.2.val))
    (atlasEquiv_symm_component v))).mpr
  rfl

@[simp] theorem pathVertex_position {k : ℕ} (v : Vertex k) :
    pathVertex (component v).1 (component v).2 (position v)=v := by
  have h := congrArg (atlasEquiv k) (atlasEquiv_symm_eq v)
  simpa only [Equiv.apply_symm_apply,atlasEquiv_apply,atlasVertex] using h.symm

end PlanarHom.RadialPottsTile.OnionBoundary
