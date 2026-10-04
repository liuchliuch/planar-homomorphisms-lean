import PlanarHom.RadialPottsAssemblyCircleCoordinates

/-! Simultaneous strict ray-order preservation under finite ribbon narrowing.
All real transverse heights are covered by four endpoint determinants, so the
existence proof uses only finite continuity conditions. -/
noncomputable section
open Set Filter unitInterval
open scoped Topology
namespace PlanarHom.RadialPottsAssemblyGeometry
open MultiGraph Polygonal

def fanVector (D N : Plane) (width height : ℝ) : Plane := D+(width*height) • N

private theorem interp_neg {a b s : ℝ} (ha : a<0) (hb : b<0)
    (hs : 0≤s ∧ s≤1) : (1-s)*a+s*b<0 := by
  have h : (1-s)*a+s*b = a+s*(b-a) := by ring
  by_cases hab : a≤b
  · have h₁ := mul_nonneg (sub_nonneg.mpr hs.2) (sub_nonneg.mpr hab)
    nlinarith
  · have h₁ := mul_nonpos_of_nonneg_of_nonpos hs.1 (by linarith : b-a≤0)
    linarith

private theorem fan_cross_left (D N Q : Plane) (w s : ℝ) :
    cross (fanVector D N w s) Q=
      (1-s)*cross (fanVector D N w 0) Q+s*cross (fanVector D N w 1) Q := by
  simp [fanVector,cross]
  ring

private theorem fan_cross_right (P D N : Plane) (w s : ℝ) :
    cross P (fanVector D N w s)=
      (1-s)*cross P (fanVector D N w 0)+s*cross P (fanVector D N w 1) := by
  simp [fanVector,cross]
  ring

theorem fan_cross_negative (D N Q M : Plane) (w : ℝ)
    (h : ∀ b c : Bool,cross (fanVector D N w (if b then 1 else 0))
      (fanVector Q M w (if c then 1 else 0))<0)
    (s t : I) : cross (fanVector D N w s) (fanVector Q M w t)<0 := by
  rw [fan_cross_left]
  apply interp_neg
  · rw [fan_cross_right]
    exact interp_neg (h false false) (h false true) t.2
  · rw [fan_cross_right]
    exact interp_neg (h true false) (h true true) t.2
  · exact s.2

theorem fan_x_same_sign (D N : Plane) (w : ℝ) (hD : D.1≠0)
    (h : 0<D.1*(fanVector D N w 1).1) (s : I) :
    0<D.1*(fanVector D N w s).1 := by
  have hd : 0<D.1^2 := sq_pos_of_ne_zero hD
  have hneg := interp_neg (neg_neg_of_pos hd) (neg_neg_of_pos h) s.2
  dsimp [fanVector] at hneg ⊢
  nlinarith

/-- A single positive narrowing factor preserves every requested strict
clockwise pair and the horizontal sign of every ray, for all heights. -/
theorem exists_narrow_fans {A : Type*} [Finite A] (D N : A→Plane)
    (hD : ∀ a,(D a).1≠0) (R : A→A→Prop) (hR : ∀ a b,R a b→cross (D a) (D b)<0) :
    ∃ width : ℝ,0<width ∧ width<1 ∧
      (∀ a (s : I),0<(D a).1*(fanVector (D a) (N a) width s).1) ∧
      (∀ a b,R a b→∀ s t : I,
        cross (fanVector (D a) (N a) width s) (fanVector (D b) (N b) width t)<0) := by
  classical
  have hx : ∀ a,∀ᶠ w : ℝ in 𝓝 0,0<(D a).1*(fanVector (D a) (N a) w 1).1 := by
    intro a
    apply (isOpen_lt continuous_const (show Continuous (fun w : ℝ =>
      (D a).1*(fanVector (D a) (N a) w 1).1) by unfold fanVector; fun_prop)).mem_nhds
    simpa [fanVector,pow_two] using sq_pos_of_ne_zero (hD a)
  have hc : ∀ a b (s t : Bool),∀ᶠ w : ℝ in 𝓝 0,R a b→
      cross (fanVector (D a) (N a) w (if s then 1 else 0))
        (fanVector (D b) (N b) w (if t then 1 else 0))<0 := by
    intro a b s t
    by_cases hab : R a b
    · have hh : ∀ᶠ w : ℝ in 𝓝 0,
          cross (fanVector (D a) (N a) w (if s then 1 else 0))
            (fanVector (D b) (N b) w (if t then 1 else 0))<0 := by
        apply (isOpen_lt (show Continuous (fun w : ℝ =>
          cross (fanVector (D a) (N a) w (if s then 1 else 0))
            (fanVector (D b) (N b) w (if t then 1 else 0))) by unfold fanVector cross; fun_prop)
          continuous_const).mem_nhds
        simpa [fanVector] using hR a b hab
      exact hh.mono (fun _ h _ => h)
    · exact Filter.Eventually.of_forall (fun _ h => (hab h).elim)
  have hallx := Filter.eventually_all.mpr hx
  have hallc := Filter.eventually_all.mpr (fun a => Filter.eventually_all.mpr
    (fun b => Filter.eventually_all.mpr (fun s => Filter.eventually_all.mpr (hc a b s))))
  have hu : ∀ᶠ w : ℝ in 𝓝 0,w<1 := isOpen_Iio.mem_nhds (by norm_num : (0:ℝ)<1)
  have hp : ∀ᶠ w : ℝ in 𝓝[>] 0,0<w := self_mem_nhdsWithin
  obtain ⟨w,hw,hw1,hwx,hwc⟩ := (hp.and ((hu.and (hallx.and hallc)).filter_mono nhdsWithin_le_nhds)).exists
  refine ⟨w,hw,hw1,fun a s => fan_x_same_sign _ _ w (hD a) (hwx a) s,?_⟩
  intro a b hab s t
  exact fan_cross_negative _ _ _ _ w (fun u v => hwc a b u v hab) s t

end PlanarHom.RadialPottsAssemblyGeometry
