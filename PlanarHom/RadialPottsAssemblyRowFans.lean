import PlanarHom.RadialPottsAssemblyFanOrder

/-! From finite clockwise ray rows to strictly ordered actual circular ports.
Each ribbon's target reverses its transverse order, exactly as the bar tile's
four end bundles do. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph Polygonal

def orientedLevel {m : ℕ} (level : Fin m→I) (forward : Bool) (i : Fin m) : I :=
  if forward then unitInterval.symm (level i) else level i

def rowPort {n m : ℕ} (D N : Fin n→Plane) (forward : Fin n→Bool)
    (level : Fin m→I) (width : ℝ) (v : Fin n×Fin m) : Plane :=
  fanVector (D v.1) (N v.1) width (orientedLevel level (forward v.1) v.2)

theorem flatRank_lt_iff {n m : ℕ} (u v : Fin n×Fin m) :
    (finProdFinEquiv u).val<(finProdFinEquiv v).val ↔
      u.1.val<v.1.val ∨ (u.1.val=v.1.val ∧ u.2.val<v.2.val) := by
  change u.2.val+m*u.1.val<v.2.val+m*v.1.val ↔ _
  have hu := u.2.isLt
  have hv := v.2.isLt
  have hm : ∀ i j : ℕ,i<j→m*i+m≤m*j := by
    intro i j hij
    have h := Nat.mul_le_mul_left m (show i+1≤j by omega)
    simpa only [Nat.mul_add,Nat.mul_one] using h
  rcases lt_trichotomy u.1.val v.1.val with h | h | h
  · have hh := hm _ _ h
    omega
  · simp [h]
  · have hh := hm _ _ h
    omega

private theorem fan_cross_same (D N : Plane) (w s t : ℝ) :
    cross (fanVector D N w s) (fanVector D N w t)=w*(t-s)*cross D N := by
  simp [fanVector,cross]
  ring

theorem rowPort_same_clockwise {n m : ℕ} (D N : Fin n→Plane) (forward : Fin n→Bool)
    (level : Fin m→I) (hlevel : StrictMono level) (width : ℝ) (hw : 0<width)
    (hside : ∀ i,if forward i then 0<cross (D i) (N i) else cross (D i) (N i)<0)
    (i : Fin n) (a b : Fin m) (hab : a<b) :
    cross (rowPort D N forward level width (i,a)) (rowPort D N forward level width (i,b))<0 := by
  have hl : (level a:ℝ)<(level b:ℝ) := hlevel hab
  have hs := hside i
  unfold rowPort
  rw [fan_cross_same]
  cases h : forward i
  · simp only [h,Bool.false_eq_true,if_false] at hs
    simp only [orientedLevel,Bool.false_eq_true,if_false]
    exact mul_neg_of_pos_of_neg (mul_pos hw (sub_pos.mpr hl)) hs
  · simp only [h,if_true] at hs
    simp only [orientedLevel,if_true,unitInterval.coe_symm_eq]
    have hh : 1-(level b:ℝ)-(1-(level a:ℝ))<0 := by linarith
    exact mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hw hh) hs

/-- Fixed-width version, allowing one globally chosen narrowing factor to
serve both endpoints of every original occurrence. -/
theorem row_ports_clockwise {n m : ℕ} (D N : Fin n→Plane)
    (forward : Fin n→Bool) (level : Fin m→I) (hlevel : StrictMono level)
    (hD : ∀ i,(D i).1≠0)
    (hside : ∀ i,if forward i then 0<cross (D i) (N i) else cross (D i) (N i)<0)
    (hrow : ∀ i j,i<j→
      (0<(D i).1 ∧ 0<(D j).1 ∧ cross (D i) (D j)<0) ∨
      (0<(D i).1 ∧ (D j).1<0))
    (w : ℝ) (hw : 0<w)
    (hx : ∀ i (s : I),0<(D i).1*(fanVector (D i) (N i) w s).1)
    (hcross : ∀ i j,i<j ∧ 0<(D i).1 ∧ 0<(D j).1→∀ s t : I,
      cross (fanVector (D i) (N i) w s) (fanVector (D j) (N j) w t)<0) :
    (∀ v : Fin n×Fin m,(rowPort D N forward level w v).1≠0) ∧
      StrictAnti (fun z : Fin (n*m) =>
        circleHeight (rowPort D N forward level w (finProdFinEquiv.symm z))) := by
  have hs : ∀ v : Fin n×Fin m,0<(D v.1).1*(rowPort D N forward level w v).1 := by
    intro v
    exact hx v.1 (orientedLevel level (forward v.1) v.2)
  have hn : ∀ v : Fin n×Fin m,(rowPort D N forward level w v).1≠0 := by
    intro v h
    have hh := hs v
    rw [h,mul_zero] at hh
    exact lt_irrefl _ hh
  refine ⟨hn,?_⟩
  intro z z' hzz
  let v : Fin n×Fin m := finProdFinEquiv.symm z
  let v' : Fin n×Fin m := finProdFinEquiv.symm z'
  have hv : (finProdFinEquiv v).val<(finProdFinEquiv v').val := by
    change (finProdFinEquiv (finProdFinEquiv.symm z)).val<(finProdFinEquiv (finProdFinEquiv.symm z')).val
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    exact hzz
  change circleHeight (rowPort D N forward level w v')<circleHeight (rowPort D N forward level w v)
  rcases (flatRank_lt_iff v v').mp hv with hij | ⟨hij,hab⟩
  · rcases hrow v.1 v'.1 hij with hh | hh
    · have hp : 0<(rowPort D N forward level w v).1 := by nlinarith [hs v,hh.1]
      have hq : 0<(rowPort D N forward level w v').1 := by nlinarith [hs v',hh.2.1]
      apply circleHeight_clockwise (mul_pos hp hq)
      exact hcross v.1 v'.1 ⟨hij,hh.1,hh.2.1⟩ _ _
    · have hp : 0<(rowPort D N forward level w v).1 := by nlinarith [hs v,hh.1]
      have hq : (rowPort D N forward level w v').1<0 := by nlinarith [hs v',hh.2]
      have hhp := (circleHeight_sign (hn v)).1.mpr hp
      have hhq := (circleHeight_sign (hn v')).2.mpr hq
      linarith
  · have hi : v.1=v'.1 := Fin.ext hij
    have hsame : 0<(rowPort D N forward level w v).1*(rowPort D N forward level w v').1 := by
      have hp := hs v
      have hq := hs v'
      rw [← hi] at hq
      rcases lt_or_gt_of_ne (hD v.1) with hh | hh
      · exact mul_pos_of_neg_of_neg (by nlinarith) (by nlinarith)
      · exact mul_pos (by nlinarith) (by nlinarith)
    apply circleHeight_clockwise hsame
    have he : v'=(v.1,v'.2) := Prod.ext hi.symm rfl
    rw [he]
    exact rowPort_same_clockwise D N forward level hlevel w hw hside v.1 v.2 v'.2 hab


/-- All-rightward rows, optionally followed by a single leftward parent,
have an actual common thinning whose circular ports are strictly clockwise. -/
theorem exists_clockwise_row_ports {n m : ℕ} (D N : Fin n→Plane)
    (forward : Fin n→Bool) (level : Fin m→I) (hlevel : StrictMono level)
    (hD : ∀ i,(D i).1≠0)
    (hside : ∀ i,if forward i then 0<cross (D i) (N i) else cross (D i) (N i)<0)
    (hrow : ∀ i j,i<j→
      (0<(D i).1 ∧ 0<(D j).1 ∧ cross (D i) (D j)<0) ∨
      (0<(D i).1 ∧ (D j).1<0)) :
    ∃ width : ℝ,0<width ∧ width<1 ∧
      (∀ v : Fin n×Fin m,(rowPort D N forward level width v).1≠0) ∧
      StrictAnti (fun z : Fin (n*m) =>
        circleHeight (rowPort D N forward level width (finProdFinEquiv.symm z))) := by
  let R : Fin n→Fin n→Prop := fun i j => i<j ∧ 0<(D i).1 ∧ 0<(D j).1
  have hR : ∀ i j,R i j→cross (D i) (D j)<0 := by
    intro i j h
    rcases hrow i j h.1 with hh | hh
    · exact hh.2.2
    · linarith [h.2.2,hh.2]
  obtain ⟨w,hw,hw1,hx,hcross⟩ := exists_narrow_fans D N hD R hR
  obtain ⟨hn,ha⟩ := row_ports_clockwise D N forward level hlevel hD hside hrow w hw hx hcross
  exact ⟨w,hw,hw1,hn,ha⟩

end PlanarHom.RadialPottsAssemblyGeometry
