import PlanarHom.PlanarGadgetInsertion
import PlanarHom.RectangularDoubleDiamondGraph

/-! NEW literal eight-occurrence mixed double diamond and its actual strip
embedding. Both terminals, all five private vertices and all eight occurrences
are explicit; no planar certificate is required as an input. -/
noncomputable section
open Classical
open unitInterval
namespace PlanarHom.RectangularMixedGadgets
open MultiGraph

private def quarter : I := ⟨1/4,by norm_num⟩
private def half : I := ⟨1/2,by norm_num⟩
private def threeQuarters : I := ⟨3/4,by norm_num⟩
private def point : Bool⊕Fin 5→I×I :=
  Sum.elim (fun b=>if b then (1,0) else (0,0))
    ![(quarter,quarter),(quarter,threeQuarters),(half,half),
      (threeQuarters,quarter),(threeQuarters,threeQuarters)]
private def blend (a b t : I) : I :=
  ⟨(1-(t:ℝ))*(a:ℝ)+(t:ℝ)*(b:ℝ),by
    refine ⟨add_nonneg (mul_nonneg (sub_nonneg.mpr t.property.2) a.property.1)
      (mul_nonneg t.property.1 b.property.1),?_⟩
    have h₁ := mul_le_mul_of_nonneg_left a.property.2 (sub_nonneg.mpr t.property.2)
    have h₂ := mul_le_mul_of_nonneg_left b.property.2 t.property.1
    nlinarith⟩
private def curve (e : Fin 8) : C(I,I×I) where
  toFun t := (blend (point (doubleDiamond.src e)).1 (point (doubleDiamond.dst e)).1 t,
    blend (point (doubleDiamond.src e)).2 (point (doubleDiamond.dst e)).2 t)
  continuous_toFun := by
    apply Continuous.prodMk <;> apply Continuous.subtype_mk <;>
      change Continuous (fun t:I=>(1-(t:ℝ))*_+(t:ℝ)*_) <;> fun_prop

set_option maxHeartbeats 8000000 in
private def strip : TwoTerminal.StripDrawing doubleDiamond where
  point := point
  point_injective := by
    rintro (a|a) (b|b) h
    · cases a <;> cases b <;> norm_num [point,quarter,half,threeQuarters,Prod.ext_iff,Subtype.ext_iff] at h <;> rfl
    · cases a <;> fin_cases b <;> norm_num [point,quarter,half,threeQuarters,Prod.ext_iff,Subtype.ext_iff] at h <;> rfl
    · fin_cases a <;> cases b <;> norm_num [point,quarter,half,threeQuarters,Prod.ext_iff,Subtype.ext_iff] at h <;> rfl
    · fin_cases a <;> fin_cases b <;> norm_num [point,quarter,half,threeQuarters,Prod.ext_iff,Subtype.ext_iff] at h <;> rfl
  left := rfl
  right := rfl
  internal_inside := by intro k; fin_cases k <;> norm_num [point,quarter,half,threeQuarters,Inside]
  curve := curve
  curve_zero := by intro e; ext <;> simp [curve,blend]
  curve_one := by intro e; ext <;> simp [curve,blend]
  curve_inside := by
    intro e t ht
    rcases ht with ⟨ht₀,ht₁⟩
    have htpos : (0:I)<t := ht₀
    have htlt : t<(1:I) := ht₁
    fin_cases e <;> norm_num [curve,blend,point,doubleDiamond,quarter,half,threeQuarters,Inside]
    all_goals try dsimp at *
    all_goals constructor <;> first | assumption | linarith
  interior_injective := by
    intro e f s t hs ht h
    have hx := congrArg (fun p:I×I=>(p.1:ℝ)) h
    have hy := congrArg (fun p:I×I=>(p.2:ℝ)) h
    rcases hs with ⟨hs₀,hs₁⟩
    rcases ht with ⟨ht₀,ht₁⟩
    fin_cases e <;> fin_cases f <;>
      norm_num [curve,blend,point,doubleDiamond,quarter,half,threeQuarters] at hx hy ⊢
    all_goals try dsimp at hx hy
    all_goals norm_num at hx hy ⊢
    all_goals first | (apply Subtype.ext; linarith) | linarith
  interior_avoids := by
    intro e t ht v h
    have hx := congrArg (fun p:I×I=>(p.1:ℝ)) h
    have hy := congrArg (fun p:I×I=>(p.2:ℝ)) h
    rcases ht with ⟨ht₀,ht₁⟩
    have hn0 : t ≠ (0:I) := ne_of_gt (show (0:I)<t from ht₀)
    have hn1 : t ≠ (1:I) := ne_of_lt (show t<(1:I) from ht₁)
    fin_cases e <;> rcases v with (b|k)
    all_goals first
      | (cases b <;> norm_num [curve,blend,point,doubleDiamond,quarter,half,threeQuarters] at hx hy <;> (try dsimp at hx hy) <;> norm_num at hx hy <;> first | exact hn0 hx | exact hn1 hx | linarith)
      | (fin_cases k <;> norm_num [curve,blend,point,doubleDiamond,quarter,half,threeQuarters] at hx hy <;> (try dsimp at hx hy) <;> norm_num at hx hy <;> first | exact hn0 hx | exact hn1 hx | linarith)

theorem doubleDiamond_planarEdgeGadget : TwoTerminal.PlanarEdgeGadget doubleDiamond :=
  strip.planarEdgeGadget

end PlanarHom.RectangularMixedGadgets
