import PlanarHom.OccurrenceKasteleynContourSides

/-! NEW literal circle corner arcs, including the gap crossing the chart pole.
Homogeneous rational coordinates stay continuous at infinity; no missing
wraparound path or circular-order certificate is assumed. -/
noncomputable section
open Set Topology unitInterval
namespace PlanarHom.CircleBoundaryArcs
open MultiGraph RadialPottsAssemblyGeometry PlanarityCircleCrossing

def boundaryPoint (u v : ℝ) : Plane :=
  (2*u*v/(u^2+v^2),(v^2-u^2)/(u^2+v^2))

theorem boundaryPoint_norm_sq (u v : ℝ) (h : u^2+v^2≠0) :
    (boundaryPoint u v).1^2+(boundaryPoint u v).2^2=1 := by
  dsimp [boundaryPoint]
  field_simp
  ring

theorem boundaryPoint_circle (u v : ℝ) (h : u^2+v^2≠0) : rayLength (boundaryPoint u v)=1 := by
  have hh := rayLength_sq (boundaryPoint u v)
  rw [boundaryPoint_norm_sq u v h] at hh
  nlinarith [rayLength_nonneg (boundaryPoint u v)]

theorem boundaryPoint_cayley {u : ℝ} (v : ℝ) (hu : u≠0) :
    boundaryPoint u v=diskMap (0,v/u) := by
  apply Prod.ext <;> dsimp [boundaryPoint,diskMap,cayleyDen] <;> field_simp <;> ring

theorem boundaryPoint_pole_iff (u v : ℝ) (h : u^2+v^2≠0) :
    boundaryPoint u v=(0,1) ↔ u=0 := by
  constructor
  · intro he
    have hh := congrArg Prod.snd he
    change (v^2-u^2)/(u^2+v^2)=1 at hh
    have hn := (div_eq_iff h).mp hh
    nlinarith [sq_nonneg u]
  · intro hu
    subst u
    simpa [boundaryPoint] using (show (0:ℝ)=0 ∧ v^2/v^2=1 by
      constructor
      · rfl
      · exact div_self (by simpa using h))

private theorem arc_den_pos (a k : ℝ) (hk : k≠0) (t : I) :
    0<(1-(t:ℝ))^2+(a*(1-(t:ℝ))+k*(t:ℝ))^2 := by
  by_cases ht : (t:ℝ)=1
  · simp only [ht,sub_self,mul_zero,mul_one,zero_add,zero_pow (by norm_num : 2≠0)]
    exact sq_pos_of_ne_zero hk
  · have hn : 1-(t:ℝ)≠0 := sub_ne_zero.mpr (fun h => ht h.symm)
    nlinarith [sq_pos_of_ne_zero hn,sq_nonneg (a*(1-(t:ℝ))+k*(t:ℝ))]

/-- From finite height a to the omitted north pole, with the sign of k selecting
which side of infinity is approached. The denominator remains strictly positive. -/
def northArc (a k : ℝ) (hk : k≠0) : C(I,Plane) where
  toFun t := boundaryPoint (1-(t:ℝ)) (a*(1-(t:ℝ))+k*(t:ℝ))
  continuous_toFun := by
    have hd : ∀ t : I, (1-(t:ℝ))^2+(a*(1-(t:ℝ))+k*(t:ℝ))^2≠0 :=
      fun t => (arc_den_pos a k hk t).ne'
    unfold boundaryPoint
    apply Continuous.prodMk <;> apply Continuous.div <;> first | exact hd | fun_prop

@[simp] theorem northArc_zero (a k : ℝ) (hk : k≠0) : northArc a k hk 0=diskMap (0,a) := by
  dsimp only [northArc,ContinuousMap.coe_mk]
  change boundaryPoint (1-(0:ℝ)) (a*(1-(0:ℝ))+k*(0:ℝ))=diskMap (0,a)
  simpa only [sub_zero,mul_one,mul_zero,add_zero,div_one] using boundaryPoint_cayley a (by norm_num : (1:ℝ)≠0)

@[simp] theorem northArc_one (a k : ℝ) (hk : k≠0) : northArc a k hk 1=(0,1) := by
  apply (boundaryPoint_pole_iff _ _ (arc_den_pos a k hk 1).ne').mpr
  norm_num

theorem northArc_circle (a k : ℝ) (hk : k≠0) (t : I) : rayLength (northArc a k hk t)=1 :=
  boundaryPoint_circle _ _ (arc_den_pos a k hk t).ne'

theorem northArc_eq_pole_iff (a k : ℝ) (hk : k≠0) (t : I) :
    northArc a k hk t=(0,1) ↔ t=1 := by
  change boundaryPoint (1-(t:ℝ)) (a*(1-(t:ℝ))+k*(t:ℝ))=(0,1) ↔ t=1
  rw [boundaryPoint_pole_iff _ _ (arc_den_pos a k hk t).ne']
  constructor
  · intro h
    apply Subtype.ext
    dsimp
    linarith
  · rintro rfl
    norm_num

theorem northArc_finite (a k : ℝ) (hk : k≠0) {t : I} (ht : t≠1) :
    northArc a k hk t=diskMap (0,a+k*((t:ℝ)/(1-(t:ℝ)))) := by
  have hd : 1-(t:ℝ)≠0 := by
    intro h
    apply ht
    apply Subtype.ext
    dsimp
    linarith
  change boundaryPoint (1-(t:ℝ)) (a*(1-(t:ℝ))+k*(t:ℝ))=_
  rw [boundaryPoint_cayley _ hd]
  congr 2
  field_simp

theorem diskMap_boundary_injective : Function.Injective (fun a : ℝ => diskMap (0,a)) := by
  intro a b h
  have hh : ((0:ℝ),a)=(0,b) := diskMap_injOn (by simp) (by simp) h
  exact congrArg Prod.snd hh

theorem northArc_injective (a k : ℝ) (hk : k≠0) : Function.Injective (northArc a k hk) := by
  intro s t h
  by_cases hs : s=1
  · subst s
    exact ((northArc_eq_pole_iff a k hk t).mp (h.symm.trans (northArc_one a k hk))).symm
  by_cases ht : t=1
  · subst t
    exact (northArc_eq_pole_iff a k hk s).mp (h.trans (northArc_one a k hk))
  rw [northArc_finite a k hk hs,northArc_finite a k hk ht] at h
  have he := diskMap_boundary_injective h
  have he' : (s:ℝ)/(1-(s:ℝ))=(t:ℝ)/(1-(t:ℝ)) := mul_left_cancel₀ hk (add_left_cancel he)
  have hsD : 1-(s:ℝ)≠0 := by intro h; apply hs; apply Subtype.ext; dsimp; linarith
  have htD : 1-(t:ℝ)≠0 := by intro h; apply ht; apply Subtype.ext; dsimp; linarith
  have hx := (div_eq_div_iff hsD htD).mp he'
  apply Subtype.ext
  nlinarith

/-- Actual endpoint-typed arc through positive or negative infinity. -/
def northPath (a k : ℝ) (hk : k≠0) : Path (diskMap (0,a)) (0,1) where
  toContinuousMap := northArc a k hk
  source' := northArc_zero a k hk
  target' := northArc_one a k hk

private theorem one_sub_pos {t : I} (ht : t≠1) : 0<1-(t:ℝ) := by
  apply sub_pos.mpr
  exact lt_of_le_of_ne t.property.2 (fun h => ht (Subtype.ext h))

/-- The two tails meet only at the omitted pole when their finite endpoints
bound a wrapping gap. -/
theorem northPaths_intersection {a b : ℝ} (hba : b<a) (x : Plane)
    (hx : x∈Set.range (northPath a 1 (by norm_num)))
    (hy : x∈Set.range (northPath b (-1) (by norm_num))) : x=(0,1) := by
  obtain ⟨s,hs⟩ := hx
  obtain ⟨t,ht⟩ := hy
  by_cases hs1 : s=1
  · subst s
    exact hs.symm.trans (northArc_one a 1 (by norm_num))
  by_cases ht1 : t=1
  · subst t
    exact ht.symm.trans (northArc_one b (-1) (by norm_num))
  have h : northArc a 1 (by norm_num) s=northArc b (-1) (by norm_num) t := hs.trans ht.symm
  rw [northArc_finite a 1 _ hs1,northArc_finite b (-1) _ ht1] at h
  have he := diskMap_boundary_injective h
  have hspos := div_nonneg s.property.1 (one_sub_pos hs1).le
  have htpos := div_nonneg t.property.1 (one_sub_pos ht1).le
  simp only [one_mul,neg_one_mul] at he
  exfalso
  linarith

/-- The full last-to-first corner, crossing the chart pole exactly once. -/
def wrappingArc (a b : ℝ) : Path (diskMap (0,a)) (diskMap (0,b)) :=
  (northPath a 1 (by norm_num)).trans (northPath b (-1) (by norm_num)).symm

theorem wrappingArc_injective {a b : ℝ} (hba : b<a) : Function.Injective (wrappingArc a b) := by
  apply Polygonal.path_trans_injective
    (northPath a 1 (by norm_num)) (northPath b (-1) (by norm_num)).symm
    (northArc_injective a 1 (by norm_num))
  · exact (northArc_injective b (-1) (by norm_num)).comp unitInterval.symm_bijective.injective
  · intro x hx hy
    rw [Path.symm_range] at hy
    exact northPaths_intersection hba x hx hy

theorem wrappingArc_circle (a b : ℝ) (t : I) : rayLength (wrappingArc a b t)=1 := by
  have hx : wrappingArc a b t∈Set.range (wrappingArc a b) := ⟨t,rfl⟩
  change wrappingArc a b t∈Set.range ((northPath a 1 (by norm_num)).trans
    (northPath b (-1) (by norm_num)).symm) at hx
  rw [Path.trans_range,Path.symm_range] at hx
  rcases hx with ⟨s,hs⟩ | ⟨s,hs⟩
  · rw [← hs]
    exact northArc_circle a 1 (by norm_num) s
  · rw [← hs]
    exact northArc_circle b (-1) (by norm_num) s

/-- An ordinary finite-height circle corner. -/
def finiteArc (a b : ℝ) : Path (diskMap (0,a)) (diskMap (0,b)) where
  toFun t := diskMap (0,AffineMap.lineMap a b (t:ℝ))
  continuous_toFun := by
    have hd : ∀ t : I, cayleyDen (0,AffineMap.lineMap a b (t:ℝ))≠0 :=
      fun t => (cayleyDen_pos _ (by simp)).ne'
    unfold diskMap
    apply Continuous.prodMk <;> apply Continuous.div
    all_goals first | exact hd | (unfold cayleyDen; fun_prop) | fun_prop
  source' := by simp
  target' := by simp

theorem finiteArc_injective {a b : ℝ} (hab : a≠b) : Function.Injective (finiteArc a b) := by
  intro s t h
  apply Subtype.ext
  exact AffineMap.lineMap_injective ℝ hab (diskMap_boundary_injective h)

theorem finiteArc_circle (a b : ℝ) (t : I) : rayLength (finiteArc a b t)=1 := by
  have hh := diskMap_boundary (AffineMap.lineMap a b (t:ℝ))
  have hs := rayLength_sq (finiteArc a b t)
  have hh' : (finiteArc a b t).1^2+(finiteArc a b t).2^2=1 := hh
  rw [hh'] at hs
  nlinarith [rayLength_nonneg (finiteArc a b t)]

end PlanarHom.CircleBoundaryArcs

