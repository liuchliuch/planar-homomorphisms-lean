import PlanarHom.RadialPottsTileBoundary

/-! A genuine incidence-preserving rectangular frame for inserting the radial
tile into a thick original-edge neighborhood. A global continuous injection
flattens the two diamond half-boundaries; no new graph edge is introduced. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph RadialPottsTile HardcoreLogicGadgets
open HardcoreLogicGadgets.IntegerDrawingCertificate

def diamondMap : C(Plane,Plane) where
  toFun p := (p.1-p.2,p.1+p.2)
  continuous_toFun := by fun_prop

theorem diamondMap_injective : Function.Injective diamondMap := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  apply Prod.ext <;> dsimp [diamondMap] at hx hy <;> linarith

def diamondDrawing (k : ℕ) : PlaneDrawing (RadialPottsTile.graph k) :=
  mapPlaneDrawing (RadialPottsTile.drawing k) diamondMap diamondMap_injective

def clamp (R x : ℝ) : ℝ := max 1 (2*R-|x|)

theorem clamp_pos (R x : ℝ) : 0<clamp R x := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

def barMap (R : ℝ) : C(Plane,Plane) where
  toFun p := (p.1,3*R*p.2/clamp R p.1)
  continuous_toFun := by
    have hn : ∀ p : Plane,clamp R p.1≠0 := fun p => ne_of_gt (clamp_pos R p.1)
    exact continuous_fst.prodMk ((continuous_const.mul continuous_snd).div
      (by unfold clamp; fun_prop) hn)

theorem barMap_injective {R : ℝ} (hR : 0<R) : Function.Injective (barMap R) := by
  intro p q h
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  change p.1=q.1 at hx
  change 3*R*p.2/clamp R p.1=3*R*q.2/clamp R q.1 at hy
  rw [hx] at hy
  apply Prod.ext hx
  exact mul_left_cancel₀ (by positivity : (3:ℝ)*R≠0)
    ((div_left_inj' (ne_of_gt (clamp_pos R q.1))).mp hy)

theorem radius_pos (k : ℕ) : 0<radius k := by unfold radius; positivity

def barDrawing (k : ℕ) : PlaneDrawing (RadialPottsTile.graph k) :=
  mapPlaneDrawing (diamondDrawing k) (barMap (radius k)) (barMap_injective (radius_pos k))

private theorem diamond_abs_le {R x y : ℝ}
    (hx : -R≤x ∧ x≤R) (hy : -R≤y ∧ y≤R) : |x-y|+|x+y|≤2*R := by
  by_cases h₁ : 0≤x-y <;> by_cases h₂ : 0≤x+y
  · rw [abs_of_nonneg h₁,abs_of_nonneg h₂]; linarith
  · rw [abs_of_nonneg h₁,abs_of_neg (by linarith : x+y<0)]; linarith
  · rw [abs_of_neg (by linarith : x-y<0),abs_of_nonneg h₂]; linarith
  · rw [abs_of_neg (by linarith : x-y<0),abs_of_neg (by linarith : x+y<0)]; linarith

private theorem diamond_abs_lt {R x y : ℝ}
    (hx : -R<x ∧ x<R) (hy : -R<y ∧ y<R) : |x-y|+|x+y|<2*R := by
  by_cases h₁ : 0≤x-y <;> by_cases h₂ : 0≤x+y
  · rw [abs_of_nonneg h₁,abs_of_nonneg h₂]; linarith
  · rw [abs_of_nonneg h₁,abs_of_neg (by linarith : x+y<0)]; linarith
  · rw [abs_of_neg (by linarith : x-y<0),abs_of_nonneg h₂]; linarith
  · rw [abs_of_neg (by linarith : x-y<0),abs_of_neg (by linarith : x+y<0)]; linarith

theorem diamond_point_bound {k : ℕ} (v : Vertex k) :
    |((diamondDrawing k).point v).1|+|((diamondDrawing k).point v).2|≤2*radius k := by
  have h := RadialPottsTile.point_bounds v
  exact diamond_abs_le ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩

theorem diamond_white_inner {k : ℕ} (w : White k) :
    |((diamondDrawing k).point (.inl w)).1|+|((diamondDrawing k).point (.inl w)).2|<2*radius k := by
  have h := RadialPottsTile.white_point_inner w
  exact diamond_abs_lt ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩

theorem diamond_curve_inner {k : ℕ} (e : Edge k) (t : I) (ht : Inside t) :
    |((diamondDrawing k).curve e t).1|+|((diamondDrawing k).curve e t).2|<2*radius k := by
  have h := RadialPottsTile.curve_interior_inside e t ht
  exact diamond_abs_lt ⟨h.1,h.2.1⟩ ⟨h.2.2.1,h.2.2.2⟩

theorem barMap_bound {R : ℝ} (hR : 0<R) (p : Plane) (hp : |p.1|+|p.2|≤2*R) :
    |(barMap R p).1|≤2*R ∧ |(barMap R p).2|≤3*R := by
  have hc : |p.2|≤clamp R p.1 := by
    have hm := le_max_right (1:ℝ) (2*R-|p.1|)
    unfold clamp
    linarith
  constructor
  · change |p.1|≤2*R
    linarith [abs_nonneg p.2]
  · change |3*R*p.2/clamp R p.1|≤3*R
    rw [abs_div,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),
      abs_of_pos hR,abs_of_pos (clamp_pos R p.1)]
    apply (div_le_iff₀ (clamp_pos R p.1)).mpr
    exact mul_le_mul_of_nonneg_left hc (by positivity)

theorem barMap_inner {R : ℝ} (hR : 0<R) (p : Plane) (hp : |p.1|+|p.2|<2*R) :
    |(barMap R p).1|<2*R ∧ |(barMap R p).2|<3*R := by
  have hc : |p.2|<clamp R p.1 := by
    have hm := le_max_right (1:ℝ) (2*R-|p.1|)
    unfold clamp
    linarith
  constructor
  · change |p.1|<2*R
    linarith [abs_nonneg p.2]
  · change |3*R*p.2/clamp R p.1|<3*R
    rw [abs_div,abs_mul,abs_mul,abs_of_pos (by norm_num : (0:ℝ)<3),
      abs_of_pos hR,abs_of_pos (clamp_pos R p.1)]
    apply (div_lt_iff₀ (clamp_pos R p.1)).mpr
    exact mul_lt_mul_of_pos_left hc (by positivity)

theorem bar_point_bound {k : ℕ} (v : Vertex k) :
    |((barDrawing k).point v).1|≤2*radius k ∧ |((barDrawing k).point v).2|≤3*radius k :=
  barMap_bound (radius_pos k) _ (diamond_point_bound v)

theorem bar_white_inner {k : ℕ} (w : White k) :
    |((barDrawing k).point (.inl w)).1|<2*radius k ∧ |((barDrawing k).point (.inl w)).2|<3*radius k :=
  barMap_inner (radius_pos k) _ (diamond_white_inner w)

theorem bar_curve_inner {k : ℕ} (e : Edge k) (t : I) (ht : Inside t) :
    |((barDrawing k).curve e t).1|<2*radius k ∧ |((barDrawing k).curve e t).2|<3*radius k :=
  barMap_inner (radius_pos k) _ (diamond_curve_inner e t ht)


theorem diamond_port_point {k : ℕ} (s : Fin 4) (a : Fin k) :
    (diamondDrawing k).point (.inr (s,a))=
      ![(20*((a.val:ℝ)-k),20*((a.val:ℝ)+1)),
        (20*((a.val:ℝ)+1),20*((k:ℝ)-a.val)),
        (20*((k:ℝ)-a.val),-20*((a.val:ℝ)+1)),
        (-20*((a.val:ℝ)+1),20*((a.val:ℝ)-k))] s := by
  change diamondMap ((RadialPottsTile.drawing k).point (.inr (s,a)))=_
  rw [port_point]
  fin_cases s <;> ext <;> simp [diamondMap,quarterTurn,realPoint,RadialPottsTileCoordinates.turn,IntegerStraightDrawing.toPlane] <;> ring

private theorem barMap_top (R u v : ℝ) (hv : 1≤v) (he : 2*R-|u|=v) :
    barMap R (u,v)=(u,3*R) := by
  change (u,3*R*v/max 1 (2*R-|u|))=(u,3*R)
  rw [he,max_eq_right hv,mul_div_cancel_right₀ _ (by linarith : v≠0)]

private theorem barMap_bottom (R u v : ℝ) (hv : v≤-1) (he : 2*R-|u|= -v) :
    barMap R (u,v)=(u,-3*R) := by
  change (u,3*R*v/max 1 (2*R-|u|))=(u,-3*R)
  rw [he,max_eq_right (by linarith : 1≤-v)]
  have hn : v≠0 := by linarith
  apply Prod.ext
  · rfl
  · dsimp
    field_simp

/-- Two bundles at each end of a literal rectangular bar. No terminal has
been identified or added: this is the same graph under a continuous injection. -/
theorem bar_port_point {k : ℕ} (s : Fin 4) (a : Fin k) :
    (barDrawing k).point (.inr (s,a))=
      ![(20*((a.val:ℝ)-k),3*radius k),
        (20*((a.val:ℝ)+1),3*radius k),
        (20*((k:ℝ)-a.val),-3*radius k),
        (-20*((a.val:ℝ)+1),-3*radius k)] s := by
  change barMap (radius k) ((diamondDrawing k).point (.inr (s,a)))=_
  rw [diamond_port_point]
  have ha : 0≤(a.val:ℝ) := by positivity
  have hak : (a.val:ℝ)+1≤k := by exact_mod_cast a.isLt
  fin_cases s
  · apply barMap_top
    · linarith
    · rw [abs_of_neg (by linarith : 20*((a.val:ℝ)-k)<0)]
      unfold radius
      ring
  · apply barMap_top
    · linarith
    · rw [abs_of_pos (by linarith : 0<20*((a.val:ℝ)+1))]
      unfold radius
      ring
  · apply barMap_bottom
    · linarith
    · rw [abs_of_pos (by linarith : 0<20*((k:ℝ)-a.val))]
      unfold radius
      ring
  · apply barMap_bottom
    · linarith
    · rw [abs_of_neg (by linarith : -20*((a.val:ℝ)+1)<0)]
      unfold radius
      ring

end PlanarHom.RadialPottsAssemblyGeometry
