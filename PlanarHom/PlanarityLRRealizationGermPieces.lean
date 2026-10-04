import PlanarHom.OccurrenceKasteleynEdgeCollars

/-!
# NEW geometry-only endpoint germ API

The declarations required by the recovered ribbon-germ consumer are proved from
literal polygonal pieces and ordinary drawing injectivity. This module makes no
claim to implement LR testing, a computed rotation, or an embedding-extraction
algorithm. Source/target piece direction is derived, never assumed as a second
certificate in addition to the actual straight germ.
-/
noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} {G : MultiGraph V E}

/-- Ordered endpoints of a literal directed occurrence. -/
def dartPair (G : MultiGraph V E) (a : Dart E) : V × V :=
  if a.2 then (G.src a.1,G.dst a.1) else (G.dst a.1,G.src a.1)

/-- The actual original curve, reversed exactly for a backward dart. -/
def PlaneDrawing.dartPath (d : PlaneDrawing G) (a : Dart E) : C(I,Plane) where
  toFun t := if a.2 then d.curve a.1 t else d.curve a.1 (unitInterval.symm t)
  continuous_toFun := by cases a.2 <;> dsimp <;> fun_prop

end PlanarHom.MultiGraph
namespace PlanarHom.PlanarityLRRealization
open MultiGraph

/-- A literal initial ray, with positive speed on one nontrivial interval. -/
def StraightGerm (p : I → Plane) (x ray : Plane) : Prop :=
  ∃ ε k : ℝ, 0<ε ∧ 0<k ∧ ∀ t : I, (t : ℝ)≤ε → p t=x+(k*(t : ℝ)) • ray

/-- A continuous interval map fixing zero takes some strictly interior positive
parameter into every positive initial neighborhood. -/
theorem exists_inside_small_parameter (f : C(I,I)) (hf : f 0=0) {ε : ℝ} (hε : 0<ε) :
    ∃ u : I, Inside u ∧ (f u : ℝ)<ε := by
  have hopen : IsOpen {u : I | (f u : ℝ)<ε} :=
    (continuous_subtype_val.comp f.continuous).isOpen_preimage _ isOpen_Iio
  have hzero : (0 : I) ∈ {u : I | (f u : ℝ)<ε} := by simpa [hf] using hε
  obtain ⟨δ,hδ,hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let x := min (δ/2) (1/2 : ℝ)
  have hx0 : 0<x := lt_min (half_pos hδ) (by norm_num)
  have hx1 : x<1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  let u : I := ⟨x,hx0.le,hx1.le⟩
  refine ⟨u,⟨hx0,hx1⟩,hball ?_⟩
  change dist (u : ℝ) (0 : ℝ)<δ
  rw [Real.dist_eq,sub_zero,abs_of_nonneg hx0.le]
  have hle : x≤δ/2 := min_le_left _ _
  change x<δ
  linarith

end PlanarHom.PlanarityLRRealization
namespace PlanarHom.MultiGraph.PolygonalDrawing
open Polygonal PlanarityLRRealization Kasteleyn
variable {V E : Type*} {G : MultiGraph V E}

/-- Every actual source piece points along the supplied positive outgoing germ. -/
theorem source_piece_direction (d : PolygonalDrawing G) (e : E) {a b : Plane}
    (hab : (a,b) ∈ (d.chain e).segments) (ha : a=d.drawing.point (G.src e)) (ray : Plane)
    (hgerm : StraightGerm (d.drawing.dartPath (e,true)) a ray) :
    ∃ c : ℝ, 0<c ∧ b-a=c • ray := by
  subst a
  obtain ⟨ε,k,hε,hk,hg⟩ := hgerm
  obtain ⟨f,hf,_,hpath⟩ := (d.chain e).segment_subpath hab
  have hpoint : d.drawing.curve e (f 0)=d.drawing.point (G.src e) := by
    rw [d.curve_eq]
    simpa using hpath 0
  have hf0 : f 0=0 := by
    rcases (d.drawing.curve_eq_point_iff e (f 0) (G.src e)).mp hpoint with ⟨h,_⟩ | ⟨h,_⟩
    · exact h
    · have hlt := hf (show (0 : I)<1 by norm_num)
      rw [h] at hlt
      exact (not_lt_of_ge (show f 1≤1 from le_top) hlt).elim
  obtain ⟨u,hu,hsmall⟩ := exists_inside_small_parameter f hf0 hε
  have hfu : 0<(f u : ℝ) := by
    have hh := hf (show (0 : I)<u from hu.1)
    rwa [hf0] at hh
  have hformula := hg (f u) hsmall.le
  change d.drawing.curve e (f u) = _ at hformula
  rw [d.curve_eq] at hformula
  change (d.chain e).strictPath (f u)=_ at hformula
  rw [hpath u] at hformula
  have hscaled : (u : ℝ) • (b-d.drawing.point (G.src e)) = (k*(f u : ℝ)) • ray := by
    calc
      _ = AffineMap.lineMap (d.drawing.point (G.src e)) b (u : ℝ)-d.drawing.point (G.src e) := by
        rw [AffineMap.lineMap_apply_module']; module
      _ = _ := by rw [hformula]; abel
  refine ⟨k*(f u : ℝ)/(u : ℝ),div_pos (mul_pos hk hfu) hu.1,?_⟩
  have hh := congrArg (fun z : Plane => (u : ℝ)⁻¹ • z) hscaled
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hu.1),one_smul,div_eq_inv_mul] using hh

/-- Every actual target piece points along the reversed positive outgoing germ. -/
theorem target_piece_direction (d : PolygonalDrawing G) (e : E) {a b : Plane}
    (hab : (a,b) ∈ (d.chain e).segments) (hb : b=d.drawing.point (G.dst e)) (ray : Plane)
    (hgerm : StraightGerm (d.drawing.dartPath (e,false)) b ray) :
    ∃ c : ℝ, 0<c ∧ a-b=c • ray := by
  subst b
  obtain ⟨ε,k,hε,hk,hg⟩ := hgerm
  obtain ⟨f,hf,_,hpath⟩ := (d.chain e).segment_subpath hab
  have hpoint : d.drawing.curve e (f 1)=d.drawing.point (G.dst e) := by
    rw [d.curve_eq]
    simpa using hpath 1
  have hf1 : f 1=1 := by
    rcases (d.drawing.curve_eq_point_iff e (f 1) (G.dst e)).mp hpoint with ⟨h,_⟩ | ⟨h,_⟩
    · have hlt := hf (show (0 : I)<1 by norm_num)
      rw [h] at hlt
      exact (not_lt_of_ge (show 0≤f 0 from bot_le) hlt).elim
    · exact h
  let g : C(I,I) := ⟨fun t => unitInterval.symm (f (unitInterval.symm t)),by fun_prop⟩
  have hg0 : g 0=0 := by simp [g,hf1]
  have hgmono : StrictMono g := by
    intro s t hst
    exact unitInterval.symm_lt_symm.mpr (hf (unitInterval.symm_lt_symm.mpr hst))
  obtain ⟨u,hu,hsmall⟩ := exists_inside_small_parameter g hg0 hε
  have hgu : 0<(g u : ℝ) := by
    have hh := hgmono (show (0 : I)<u from hu.1)
    rwa [hg0] at hh
  have hformula := hg (g u) hsmall.le
  change d.drawing.curve e (unitInterval.symm (g u)) = _ at hformula
  have hgu' : unitInterval.symm (g u)=f (unitInterval.symm u) := by simp [g]
  rw [hgu',d.curve_eq] at hformula
  change (d.chain e).strictPath (f (unitInterval.symm u))=_ at hformula
  rw [hpath (unitInterval.symm u)] at hformula
  simp only [unitInterval.coe_symm_eq,AffineMap.lineMap_apply_one_sub] at hformula
  have hscaled : (u : ℝ) • (a-d.drawing.point (G.dst e)) = (k*(g u : ℝ)) • ray := by
    calc
      _ = AffineMap.lineMap (d.drawing.point (G.dst e)) a (u : ℝ)-d.drawing.point (G.dst e) := by
        rw [AffineMap.lineMap_apply_module']; module
      _ = _ := by rw [hformula]; abel
  refine ⟨k*(g u : ℝ)/(u : ℝ),div_pos (mul_pos hk hgu) hu.1,?_⟩
  have hh := congrArg (fun z : Plane => (u : ℝ)⁻¹ • z) hscaled
  simpa only [smul_smul,inv_mul_cancel₀ (ne_of_gt hu.1),one_smul,div_eq_inv_mul] using hh

end PlanarHom.MultiGraph.PolygonalDrawing
