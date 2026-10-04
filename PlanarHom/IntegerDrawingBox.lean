import PlanarHom.IntegerStraightDrawing

/-! Exact integer rectangle certificates for open interiors of straight edges. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.IntegerStraightDrawing
open MultiGraph

def ClosedBox (H : ℕ) (p : Point) : Prop := 0≤p.1 ∧ p.1≤64 ∧ 0≤p.2 ∧ p.2≤(H:ℤ)
def OpenBox (H : ℕ) (p : Point) : Prop := 0<p.1 ∧ p.1<64 ∧ 0<p.2 ∧ p.2<(H:ℤ)
def realBox (H : ℕ) : Set Plane := {p | 0<p.1 ∧ p.1<64 ∧ 0<p.2 ∧ p.2<(H:ℝ)}
instance (H : ℕ) (p : Point) : Decidable (ClosedBox H p) := by unfold ClosedBox; infer_instance
instance (H : ℕ) (p : Point) : Decidable (OpenBox H p) := by unfold OpenBox; infer_instance

theorem openBox_cast {H : ℕ} {p : Point} (h : OpenBox H p) : toPlane p∈realBox H := by
  unfold OpenBox at h
  change (0:ℝ)<p.1 ∧ (p.1:ℝ)<64 ∧ (0:ℝ)<p.2 ∧ (p.2:ℝ)<H
  exact_mod_cast h

private theorem blend (a b M t : ℝ) (ha : 0≤a ∧ a≤M) (hb : 0≤b ∧ b≤M)
    (h : (0<a ∧ a<M) ∨ (0<b ∧ b<M)) (ht : 0<t ∧ t<1) :
    0<(1-t)*a+t*b ∧ (1-t)*a+t*b<M := by
  rcases h with h | h
  · constructor
    · nlinarith [mul_pos (show 0<1-t by linarith [ht.2]) h.1,mul_nonneg ht.1.le hb.1]
    · nlinarith [mul_pos (show 0<1-t by linarith [ht.2]) (show 0<M-a by linarith [h.2]),
        mul_nonneg ht.1.le (show 0≤M-b by linarith [hb.2])]
  · constructor
    · nlinarith [mul_nonneg (show 0≤1-t by linarith [ht.2]) ha.1,mul_pos ht.1 h.1]
    · nlinarith [mul_nonneg (show 0≤1-t by linarith [ht.2]) (show 0≤M-a by linarith [ha.2]),
        mul_pos ht.1 (show 0<M-b by linarith [h.2])]

theorem affine_in_box (H : ℕ) (a b : Point) (ha : ClosedBox H a) (hb : ClosedBox H b)
    (hi : OpenBox H a ∨ OpenBox H b) (t : I) (ht : Inside t) :
    affine (toPlane a) (toPlane b) t∈realBox H := by
  have ha' : (0:ℝ)≤a.1 ∧ (a.1:ℝ)≤64 ∧ (0:ℝ)≤a.2 ∧ (a.2:ℝ)≤H := by exact_mod_cast ha
  have hb' : (0:ℝ)≤b.1 ∧ (b.1:ℝ)≤64 ∧ (0:ℝ)≤b.2 ∧ (b.2:ℝ)≤H := by exact_mod_cast hb
  have hi' : ((0:ℝ)<a.1 ∧ (a.1:ℝ)<64 ∧ (0:ℝ)<a.2 ∧ (a.2:ℝ)<H) ∨
      ((0:ℝ)<b.1 ∧ (b.1:ℝ)<64 ∧ (0:ℝ)<b.2 ∧ (b.2:ℝ)<H) := by exact_mod_cast hi
  have hx := blend a.1 b.1 64 t ⟨ha'.1,ha'.2.1⟩ ⟨hb'.1,hb'.2.1⟩
    (hi'.imp (fun h => ⟨h.1,h.2.1⟩) (fun h => ⟨h.1,h.2.1⟩)) ht
  have hy := blend a.2 b.2 H t ha'.2.2 hb'.2.2 (hi'.imp And.right And.right |>.imp And.right And.right) ht
  exact ⟨hx.1,hx.2,hy.1,hy.2⟩

theorem drawing_curve_in_box {V E : Type} {G : MultiGraph V E} {p : V → Point}
    (cert : Certificate G p) (H : ℕ)
    (hb : ∀e,ClosedBox H (p (G.src e)) ∧ ClosedBox H (p (G.dst e)) ∧
      (OpenBox H (p (G.src e)) ∨ OpenBox H (p (G.dst e)))) :
    ∀e t,Inside t→(drawing cert).curve e t∈realBox H := by
  intro e t ht
  exact affine_in_box H _ _ (hb e).1 (hb e).2.1 (hb e).2.2 t ht

end PlanarHom.IntegerStraightDrawing
