import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! NEW elementary equality cases used in the degree-two and higher-degree
Walsh rigidity argument. These are finite sum-of-squares statements. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
variable {I:Type} [Fintype I]

theorem square_sum_add (u v:I→ℝ) :
    (∑i,(u i+v i)^2)=(∑i,u i^2)+(∑i,v i^2)+2*(∑i,u i*v i) := by
  calc
    _ = ∑i,(u i^2+v i^2+2*(u i*v i)):=by
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = _:=by simp only [Finset.sum_add_distrib,←Finset.mul_sum]

theorem unit_inner_one_forces_equal (u v:I→ℝ)
    (hu:(∑i,u i^2)=1) (hv:(∑i,v i^2)=1) (huv:(∑i,u i*v i)=1) : u=v := by
  have hs:(∑i,(u i-v i)^2)=0:=by
    calc
      _ = ∑i,(u i^2+v i^2-2*(u i*v i)):=by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = 0:=by simp only [Finset.sum_add_distrib,Finset.sum_sub_distrib,←Finset.mul_sum,hu,hv,huv];ring
  funext i
  have hi: (u i-v i)^2=0:=(Finset.sum_eq_zero_iff_of_nonneg (fun j _=>sq_nonneg (u j-v j))).mp hs i (Finset.mem_univ _)
  nlinarith

theorem norm_equality_forces_equal (u v:I→ℝ) (a:ℝ) (ha:0<a)
    (hu:(∑i,u i^2)=1) (hv:(∑i,v i^2)=1)
    (he:(∑i,(2*u i+a*v i)^2)=(2+a)^2) : u=v := by
  have hpoly:(∑i,(2*u i+a*v i)^2)=4*(∑i,u i^2)+a^2*(∑i,v i^2)+4*a*(∑i,u i*v i):=by
    calc
      _ = ∑i,(4*u i^2+a^2*v i^2+4*a*(u i*v i)):=by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _:=by simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul]
  rw [hu,hv] at hpoly
  have hi:(∑i,u i*v i)=1:=by nlinarith
  exact unit_inner_one_forces_equal u v hu hv hi

theorem unit_plus_short_max (u v:I→ℝ) (hu:(∑i,u i^2)=1)
    (hv:(∑i,v i^2)≤1) (he:(∑i,(u i+v i)^2)=4) :
    (∑i,v i^2)=1 ∧ u=v := by
  have hc:=Finset.sum_mul_sq_le_sq_mul_sq Finset.univ u v
  rw [hu] at hc
  have hadd:=square_sum_add u v
  rw [hu,he] at hadd
  have hv0:0≤∑i,v i^2:=Finset.sum_nonneg (fun i _=>sq_nonneg _)
  have hi:(∑i,u i*v i)=1:=by nlinarith [sq_nonneg ((∑i,v i^2)-1)]
  have hv1:(∑i,v i^2)=1:=by linarith
  exact ⟨hv1,unit_inner_one_forces_equal u v hu hv1 hi⟩

end PlanarHom.RectangularWalshConvolution
