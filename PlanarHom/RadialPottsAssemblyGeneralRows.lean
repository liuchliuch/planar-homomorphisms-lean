import PlanarHom.RadialPottsAssemblyRowFans

/-! NEW general clockwise rows for actual geometric source canvases.
Both open half-planes may contain arbitrary many rays. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph Polygonal

def ClockwiseRayOrder (p q : Plane) : Prop :=
  (0<p.1*q.1 ∧ cross p q<0) ∨ (0<p.1 ∧ q.1<0)

theorem clockwiseRayOrder_smul (p q : Plane) {c d : ℝ} (hc : 0<c) (hd : 0<d)
    (h : ClockwiseRayOrder p q) : ClockwiseRayOrder (c • p) (d • q) := by
  rcases h with h|h
  · left
    constructor
    · change 0<(c*p.1)*(d*q.1)
      have hh:=mul_pos (mul_pos hc hd) h.1
      nlinarith
    · rw [cross_smul_left,cross_smul_right]
      exact mul_neg_of_pos_of_neg hc (mul_neg_of_pos_of_neg hd h.2)
  · right
    exact ⟨mul_pos hc h.1,mul_neg_of_pos_of_neg hd h.2⟩

theorem row_ports_clockwise_general {n m : ℕ} (D N : Fin n→Plane)
    (forward : Fin n→Bool) (level : Fin m→I) (hlevel : StrictMono level)
    (hD : ∀ i,(D i).1≠0)
    (hside : ∀ i,if forward i then 0<cross (D i) (N i) else cross (D i) (N i)<0)
    (hrow : ∀ i j,i<j→
      ClockwiseRayOrder (D i) (D j))
    (w : ℝ) (hw : 0<w)
    (hx : ∀ i (s : I),0<(D i).1*(fanVector (D i) (N i) w s).1)
    (hcross : ∀ i j,cross (D i) (D j)<0→∀ s t : I,
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
    · have hpq : 0<(rowPort D N forward level w v).1*(rowPort D N forward level w v').1 := by
        rcases (mul_pos_iff.mp hh.1) with ⟨hp,hq⟩|⟨hp,hq⟩
        · exact mul_pos (by nlinarith [hs v]) (by nlinarith [hs v'])
        · exact mul_pos_of_neg_of_neg (by nlinarith [hs v]) (by nlinarith [hs v'])
      apply circleHeight_clockwise hpq
      exact hcross v.1 v'.1 hh.2 _ _
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



end PlanarHom.RadialPottsAssemblyGeometry
