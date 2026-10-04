import PlanarHom.ColoringMacroPointChecks

noncomputable section
open Set unitInterval
namespace PlanarHom.ColoringEmitter.MacroGeometry
open MultiGraph PositiveBlockProgram IntegerStraightDrawing

def normalizedPoint (s : CellShape) (v : LocalPatch.NumericVertex s) : Plane :=
  (((integerPoint s v).1:ℝ)/(width s:ℝ),((integerPoint s v).2:ℝ)/(width s:ℝ))

def low (s : CellShape) (x : ℝ) : ℝ := (1-x)*(s.leftLo:ℝ)+x*s.rightLo-1/4
def high (s : CellShape) (x : ℝ) : ℝ := (1-x)*(s.leftHi:ℝ)+x*s.rightHi+1/4

theorem width_real_pos (s : CellShape) : (0:ℝ)<width s := by exact_mod_cast width_pos s

theorem low_scale (s : CellShape) (p : Point) :
    low s ((p.1:ℝ)/(width s:ℝ))=(bandLow s p:ℝ)/(width s:ℝ) := by
  cases s <;> simp [low,bandLow,width,CellShape.leftLo,CellShape.rightLo] <;> ring

theorem high_scale (s : CellShape) (p : Point) :
    high s ((p.1:ℝ)/(width s:ℝ))=(bandHigh s p:ℝ)/(width s:ℝ) := by
  cases s <;> simp [high,bandHigh,width,CellShape.leftHi,CellShape.rightHi] <;> ring

theorem normalized_bound (s : CellShape) (v : LocalPatch.NumericVertex s) :
    0≤(normalizedPoint s v).1 ∧ (normalizedPoint s v).1≤1 ∧
    low s (normalizedPoint s v).1< -(normalizedPoint s v).2 ∧
    -(normalizedPoint s v).2<high s (normalizedPoint s v).1 := by
  have h := pointBound_all s v
  rcases h with ⟨hx0,hx1,hy0,hy1⟩
  have hx0' : (0:ℝ)≤(integerPoint s v).1 := by exact_mod_cast hx0
  have hx1' : ((integerPoint s v).1:ℝ)≤width s := by exact_mod_cast hx1
  have hy0' : ((bandLow s (integerPoint s v)):ℝ)< -((integerPoint s v).2:ℝ) := by exact_mod_cast hy0
  have hy1' : -((integerPoint s v).2:ℝ)<((bandHigh s (integerPoint s v)):ℝ) := by exact_mod_cast hy1
  change 0≤_/(_ : ℝ) ∧ _ ∧ _ ∧ _
  refine ⟨div_nonneg hx0' (width_real_pos s).le,(div_le_one (width_real_pos s)).mpr hx1',?_,?_⟩
  · change low s (((integerPoint s v).1:ℝ)/(width s:ℝ))< -(((integerPoint s v).2:ℝ)/(width s:ℝ))
    rw [low_scale,←neg_div]
    exact (div_lt_div_iff_of_pos_right (width_real_pos s)).mpr hy0'
  · change -(((integerPoint s v).2:ℝ)/(width s:ℝ))<high s (((integerPoint s v).1:ℝ)/(width s:ℝ))
    rw [high_scale,←neg_div]
    exact (div_lt_div_iff_of_pos_right (width_real_pos s)).mpr hy1'

theorem private_horizontal (s : CellShape) (v : LocalPatch.Private s) :
    0<(normalizedPoint s v.val).1 ∧ (normalizedPoint s v.val).1<1 := by
  have h := interiorOrPort_all s v.val
  rcases h with ⟨h0,h1⟩ | h
  · have h0' : (0:ℝ)<(integerPoint s v.val).1 := by exact_mod_cast h0
    have h1' : ((integerPoint s v.val).1:ℝ)<width s := by exact_mod_cast h1
    exact ⟨div_pos h0' (width_real_pos s),(div_lt_one (width_real_pos s)).mpr h1'⟩
  · exact False.elim (v.property h)

theorem edge_horizontal (s : CellShape) (e : LocalPatch.Edge s) :
    (0<(normalizedPoint s ((LocalPatch.numericGraph s).src e)).1 ∨
      0<(normalizedPoint s ((LocalPatch.numericGraph s).dst e)).1) ∧
    ((normalizedPoint s ((LocalPatch.numericGraph s).src e)).1<1 ∨
      (normalizedPoint s ((LocalPatch.numericGraph s).dst e)).1<1) := by
  have h := edgeInterior_all s e
  constructor
  · rcases h.1 with h | h
    · exact Or.inl (div_pos (by exact_mod_cast h) (width_real_pos s))
    · exact Or.inr (div_pos (by exact_mod_cast h) (width_real_pos s))
  · rcases h.2 with h | h
    · exact Or.inl ((div_lt_one (width_real_pos s)).mpr (by exact_mod_cast h))
    · exact Or.inr ((div_lt_one (width_real_pos s)).mpr (by exact_mod_cast h))

theorem low_affine (s : CellShape) (a b : Plane) (t : ℝ) :
    low s (affine a b t).1=(1-t)*low s a.1+t*low s b.1 := by unfold low affine; ring

theorem high_affine (s : CellShape) (a b : Plane) (t : ℝ) :
    high s (affine a b t).1=(1-t)*high s a.1+t*high s b.1 := by unfold high affine; ring

theorem affine_inside (s : CellShape) (e : LocalPatch.Edge s) (t : I) (ht : Inside t) :
    let p:=affine (normalizedPoint s ((LocalPatch.numericGraph s).src e))
      (normalizedPoint s ((LocalPatch.numericGraph s).dst e)) t
    0<p.1 ∧ p.1<1 ∧ low s p.1< -p.2 ∧ -p.2<high s p.1 := by
  have ha:=normalized_bound s ((LocalPatch.numericGraph s).src e)
  have hb:=normalized_bound s ((LocalPatch.numericGraph s).dst e)
  have he:=edge_horizontal s e
  dsimp only
  have ht0 : 0<(t:ℝ) := ht.1
  have ht1 : 0<1-(t:ℝ) := by linarith [ht.2]
  refine ⟨?_,?_,?_,?_⟩
  · dsimp [affine]
    rcases he.1 with h | h
    · nlinarith [mul_pos ht1 h,mul_nonneg ht0.le hb.1]
    · nlinarith [mul_nonneg ht1.le ha.1,mul_pos ht0 h]
  · dsimp [affine]
    rcases he.2 with h | h
    · nlinarith [mul_pos ht1 (sub_pos.mpr h),mul_nonneg ht0.le (sub_nonneg.mpr hb.2.1)]
    · nlinarith [mul_nonneg ht1.le (sub_nonneg.mpr ha.2.1),mul_pos ht0 (sub_pos.mpr h)]
  · rw [low_affine]
    dsimp [affine]
    nlinarith [mul_pos ht1 (sub_pos.mpr ha.2.2.1),mul_pos ht0 (sub_pos.mpr hb.2.2.1)]
  · rw [high_affine]
    dsimp [affine]
    nlinarith [mul_pos ht1 (sub_pos.mpr ha.2.2.2),mul_pos ht0 (sub_pos.mpr hb.2.2.2)]

end PlanarHom.ColoringEmitter.MacroGeometry
