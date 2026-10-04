import PlanarHom.RectangularNormNormalization

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWeightedNormNormalization
variable {X Y : Type} [Fintype X] [Fintype Y] [Nonempty X] [Nonempty Y]

def rowNorm (V : Matrix X Y ℝ) (ν : Y → ℝ) (x : X) : ℝ := Real.sqrt (∑ y,ν y*(V x y)^2)
def columnNorm (V : Matrix X Y ℝ) (μ : X → ℝ) (y : Y) : ℝ := Real.sqrt (∑ x,μ x*(V x y)^2)
def normalized (V : Matrix X Y ℝ) (μ : X → ℝ) (ν : Y → ℝ) : Matrix X Y ℝ :=
  fun x y => V x y/(rowNorm V ν x*columnNorm V μ y)

theorem rowNorm_pos (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y) (ν : Y → ℝ) (hν : ∀ y,0<ν y) (x : X) :
    0<rowNorm V ν x := Real.sqrt_pos.mpr
      (Finset.sum_pos (fun y _ => mul_pos (hν y) (sq_pos_of_pos (hV x y))) Finset.univ_nonempty)
theorem columnNorm_pos (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y) (μ : X → ℝ) (hμ : ∀ x,0<μ x) (y : Y) :
    0<columnNorm V μ y := Real.sqrt_pos.mpr
      (Finset.sum_pos (fun x _ => mul_pos (hμ x) (sq_pos_of_pos (hV x y))) Finset.univ_nonempty)
theorem normalized_pos (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y) :
    ∀ x y,0<normalized V μ ν x y := fun x y =>
  div_pos (hV x y) (mul_pos (rowNorm_pos V hV ν hν x) (columnNorm_pos V hV μ hμ y))

theorem rowNorm_sq (V : Matrix X Y ℝ) (ν : Y → ℝ) (hν : ∀ y,0≤ν y) (x : X) :
    (rowNorm V ν x)^2=∑ y,ν y*(V x y)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun y _ => mul_nonneg (hν y) (sq_nonneg _)))
theorem columnNorm_sq (V : Matrix X Y ℝ) (μ : X → ℝ) (hμ : ∀ x,0≤μ x) (y : Y) :
    (columnNorm V μ y)^2=∑ x,μ x*(V x y)^2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun x _ => mul_nonneg (hμ x) (sq_nonneg _)))

theorem row_unit (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y) (x : X) :
    (∑ y,ν y*(normalized V μ ν x y*columnNorm V μ y)^2)=1 := by
  have h (y : Y) : normalized V μ ν x y*columnNorm V μ y=V x y/rowNorm V ν x := by
    unfold normalized
    field_simp [ne_of_gt (columnNorm_pos V hV μ hμ y),ne_of_gt (rowNorm_pos V hV ν hν x)]
  simp_rw [h,div_pow,← mul_div_assoc]
  rw [← Finset.sum_div,← rowNorm_sq V ν (fun y => (hν y).le)]
  exact div_self (pow_ne_zero _ (ne_of_gt (rowNorm_pos V hV ν hν x)))

theorem column_unit (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y) (y : Y) :
    (∑ x,μ x*(normalized V μ ν x y*rowNorm V ν x)^2)=1 := by
  have h (x : X) : normalized V μ ν x y*rowNorm V ν x=V x y/columnNorm V μ y := by
    unfold normalized
    field_simp [ne_of_gt (columnNorm_pos V hV μ hμ y),ne_of_gt (rowNorm_pos V hV ν hν x)]
  simp_rw [h,div_pow,← mul_div_assoc]
  rw [← Finset.sum_div,← columnNorm_sq V μ (fun x => (hμ x).le)]
  exact div_self (pow_ne_zero _ (ne_of_gt (columnNorm_pos V hV μ hμ y)))

theorem proportional_unit_rows (C : Matrix X Y ℝ) (hC : ∀ x y,0<C x y)
    (weight scale : Y → ℝ) (hunit : ∀ x,∑ y,weight y*(C x y*scale y)^2=1)
    (x x' : X) (t : ℝ) (h : ∀ y,C x y=t*C x' y) : t=1 ∧ C x=C x' := by
  obtain ⟨y⟩ := ‹Nonempty Y›
  have ht : 0<t := by have := h y; have := hC x y; have := hC x' y; nlinarith
  have he : 1=t^2 := by
    calc
      1 = ∑ y,weight y*(C x y*scale y)^2 := (hunit x).symm
      _ = t^2*(∑ y,weight y*(C x' y*scale y)^2) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro y _
        rw [h y]
        ring
      _ = t^2 := by rw [hunit,mul_one]
  have ht1 : t=1 := by nlinarith
  exact ⟨ht1,funext (fun y => by simpa only [ht1,one_mul] using h y)⟩

theorem reconstruct (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y) (x : X) (y : Y) :
    V x y=rowNorm V ν x*columnNorm V μ y*normalized V μ ν x y := by
  unfold normalized
  field_simp [ne_of_gt (columnNorm_pos V hV μ hμ y),ne_of_gt (rowNorm_pos V hV ν hν x)]

theorem normalized_proportional_rows (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (x x' : X) (t : ℝ) (h : ∀ y,normalized V μ ν x y=t*normalized V μ ν x' y) :
    t=1 ∧ normalized V μ ν x=normalized V μ ν x' :=
  proportional_unit_rows _ (normalized_pos V hV μ ν hμ hν) ν (columnNorm V μ)
    (row_unit V hV μ ν hμ hν) x x' t h

theorem normalized_proportional_columns (V : Matrix X Y ℝ) (hV : ∀ x y,0<V x y)
    (μ : X → ℝ) (ν : Y → ℝ) (hμ : ∀ x,0<μ x) (hν : ∀ y,0<ν y)
    (y y' : Y) (t : ℝ) (h : ∀ x,normalized V μ ν x y=t*normalized V μ ν x y') :
    t=1 ∧ (normalized V μ ν).transpose y=(normalized V μ ν).transpose y' :=
  proportional_unit_rows (normalized V μ ν).transpose
    (fun y x => normalized_pos V hV μ ν hμ hν x y) μ (rowNorm V ν)
    (column_unit V hV μ ν hμ hν) y y' t h

end PlanarHom.RectangularWeightedNormNormalization
