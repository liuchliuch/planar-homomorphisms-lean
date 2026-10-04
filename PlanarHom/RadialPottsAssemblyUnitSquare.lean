import PlanarHom.RadialPottsAssemblyBarGeometry

/-! The literal all-k tile in a closed coordinate square, with every open edge
and white vertex strictly inside. The four terminal bundles have exact rational
transverse coordinates at the two longitudinal ends. -/
noncomputable section
open Set unitInterval
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph RadialPottsTile HardcoreLogicGadgets

def squareMap (k : ℕ) : C(Plane,Plane) where
  toFun p := ((p.2+3*radius k)/(6*radius k),(p.1+2*radius k)/(4*radius k))
  continuous_toFun := by fun_prop

theorem squareMap_injective (k : ℕ) : Function.Injective (squareMap k) := by
  intro p q h
  have hr := radius_pos k
  have hx := congrArg Prod.fst h
  have hy := congrArg Prod.snd h
  dsimp [squareMap] at hx hy
  have hx' := (div_left_inj' (by positivity : (6:ℝ)*radius k≠0)).mp hx
  have hy' := (div_left_inj' (by positivity : (4:ℝ)*radius k≠0)).mp hy
  apply Prod.ext <;> linarith

def squareDrawing (k : ℕ) : PlaneDrawing (RadialPottsTile.graph k) :=
  mapPlaneDrawing (barDrawing k) (squareMap k) (squareMap_injective k)

private theorem square_bounds {k : ℕ} {p : Plane}
    (hp : |p.1|≤2*radius k ∧ |p.2|≤3*radius k) :
    (squareMap k p).1∈Set.Icc (0:ℝ) 1 ∧ (squareMap k p).2∈Set.Icc (0:ℝ) 1 := by
  have hr := radius_pos k
  have hx := abs_le.mp hp.1
  have hy := abs_le.mp hp.2
  change (0≤(p.2+3*radius k)/(6*radius k) ∧ (p.2+3*radius k)/(6*radius k)≤1) ∧
    (0≤(p.1+2*radius k)/(4*radius k) ∧ (p.1+2*radius k)/(4*radius k)≤1)
  constructor <;> constructor
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_one (by positivity : (0:ℝ)<6*radius k)).mpr; linarith
  · exact div_nonneg (by linarith) (by positivity)
  · apply (div_le_one (by positivity : (0:ℝ)<4*radius k)).mpr; linarith

private theorem square_inside {k : ℕ} {p : Plane}
    (hp : |p.1|<2*radius k ∧ |p.2|<3*radius k) :
    (0<(squareMap k p).1 ∧ (squareMap k p).1<1) ∧
    (0<(squareMap k p).2 ∧ (squareMap k p).2<1) := by
  have hr := radius_pos k
  have hx := abs_lt.mp hp.1
  have hy := abs_lt.mp hp.2
  change (0<(p.2+3*radius k)/(6*radius k) ∧ (p.2+3*radius k)/(6*radius k)<1) ∧
    (0<(p.1+2*radius k)/(4*radius k) ∧ (p.1+2*radius k)/(4*radius k)<1)
  constructor <;> constructor
  · exact div_pos (by linarith) (by positivity)
  · apply (div_lt_one (by positivity : (0:ℝ)<6*radius k)).mpr; linarith
  · exact div_pos (by linarith) (by positivity)
  · apply (div_lt_one (by positivity : (0:ℝ)<4*radius k)).mpr; linarith

theorem square_point_bounds {k : ℕ} (v : Vertex k) :
    ((squareDrawing k).point v).1∈Set.Icc (0:ℝ) 1 ∧
    ((squareDrawing k).point v).2∈Set.Icc (0:ℝ) 1 := square_bounds (bar_point_bound v)

theorem square_white_inside {k : ℕ} (w : White k) :
    (0<((squareDrawing k).point (.inl w)).1 ∧ ((squareDrawing k).point (.inl w)).1<1) ∧
    (0<((squareDrawing k).point (.inl w)).2 ∧ ((squareDrawing k).point (.inl w)).2<1) :=
  square_inside (bar_white_inner w)

theorem square_curve_inside {k : ℕ} (e : Edge k) (t : I) (ht : Inside t) :
    (0<((squareDrawing k).curve e t).1 ∧ ((squareDrawing k).curve e t).1<1) ∧
    (0<((squareDrawing k).curve e t).2 ∧ ((squareDrawing k).curve e t).2<1) :=
  square_inside (bar_curve_inner e t ht)

theorem square_curve_bounds {k : ℕ} (e : Edge k) (t : I) :
    ((squareDrawing k).curve e t).1∈Set.Icc (0:ℝ) 1 ∧
    ((squareDrawing k).curve e t).2∈Set.Icc (0:ℝ) 1 := by
  by_cases h0 : t=0
  · rw [h0,(squareDrawing k).curve_zero]; exact square_point_bounds _
  by_cases h1 : t=1
  · rw [h1,(squareDrawing k).curve_one]; exact square_point_bounds _
  have h : Inside t := by
    have hh0 : (t:ℝ)≠0 := fun h => h0 (Subtype.ext h)
    have hh1 : (t:ℝ)≠1 := fun h => h1 (Subtype.ext h)
    exact ⟨lt_of_le_of_ne t.2.1 (Ne.symm hh0),lt_of_le_of_ne t.2.2 hh1⟩
  have hi := square_curve_inside e t h
  exact ⟨⟨hi.1.1.le,hi.1.2.le⟩,⟨hi.2.1.le,hi.2.2.le⟩⟩

def squarePoint {k : ℕ} (v : Vertex k) : I×I :=
  (⟨((squareDrawing k).point v).1,(square_point_bounds v).1⟩,
   ⟨((squareDrawing k).point v).2,(square_point_bounds v).2⟩)

def squareCurve {k : ℕ} (e : Edge k) : C(I,I×I) where
  toFun t := (⟨((squareDrawing k).curve e t).1,(square_curve_bounds e t).1⟩,
    ⟨((squareDrawing k).curve e t).2,(square_curve_bounds e t).2⟩)
  continuous_toFun := (((squareDrawing k).curve e).continuous.fst.subtype_mk _).prodMk
    (((squareDrawing k).curve e).continuous.snd.subtype_mk _)

@[simp] theorem squareCurve_zero {k : ℕ} (e : Edge k) :
    squareCurve e 0=squarePoint ((RadialPottsTile.graph k).src e) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst ((squareDrawing k).curve_zero e)
  · exact congrArg Prod.snd ((squareDrawing k).curve_zero e)

@[simp] theorem squareCurve_one {k : ℕ} (e : Edge k) :
    squareCurve e 1=squarePoint ((RadialPottsTile.graph k).dst e) := by
  apply Prod.ext <;> apply Subtype.ext
  · exact congrArg Prod.fst ((squareDrawing k).curve_one e)
  · exact congrArg Prod.snd ((squareDrawing k).curve_one e)

/-- Exact end positions, with longitudinal coordinate first. -/
theorem square_port_point {k : ℕ} (s : Fin 4) (a : Fin k) :
    (squareDrawing k).point (.inr (s,a))=
      ![(1,((a.val:ℝ)+1)/(2*((k:ℝ)+1))),
        (1,((k:ℝ)+a.val+2)/(2*((k:ℝ)+1))),
        (0,(2*(k:ℝ)-a.val+1)/(2*((k:ℝ)+1))),
        (0,((k:ℝ)-a.val)/(2*((k:ℝ)+1)))] s := by
  change squareMap k ((barDrawing k).point (.inr (s,a)))=_
  rw [bar_port_point]
  have hn : (k:ℝ)+1≠0 := by positivity
  fin_cases s <;> apply Prod.ext <;> simp [squareMap,radius] <;> field_simp <;> ring

end PlanarHom.RadialPottsAssemblyGeometry
