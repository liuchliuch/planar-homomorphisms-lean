import PlanarHom.PositiveRealCoreGrams
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic

/-! NEW strict positive-kernel scaling rigidity. If a positive matrix has the
same positive row and column sum, two diagonal scalings giving constant row
and column sums must themselves be constant. This retains the two independent
side constants required by the bipartite weighted theorem. -/
noncomputable section
set_option autoImplicit false
open Classical
open scoped BigOperators
namespace PlanarHom.PositiveKernelScalingRigidity
variable {I : Type} [Fintype I] [Nonempty I]

theorem constant_scalings (K : Matrix I I ℝ) (hK : ∀i j,0<K i j)
    (R : ℝ) (hR : 0<R) (hrow : ∀i,∑j,K i j=R) (hcol : ∀j,∑i,K i j=R)
    (μ ν : I → ℝ) (hμ : ∀i,0<μ i) (hν : ∀i,0<ν i)
    (c d : ℝ) (hleft : ∀i,μ i*(∑j,K i j*ν j)=c)
    (hright : ∀j,ν j*(∑i,K i j*μ i)=d) :
    (∀i j,μ i=μ j) ∧ (∀i j,ν i=ν j) := by
  have htot : (∑i,μ i*(∑j,K i j*ν j)) = ∑j,ν j*(∑i,K i j*μ i) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hcd : c=d := by
    simp only [hleft,hright,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at htot
    exact mul_left_cancel₀ (by exact_mod_cast (Fintype.card_pos : 0<Fintype.card I).ne') htot
  obtain ⟨i,hi,hmax⟩ := Finset.exists_max_image Finset.univ μ Finset.univ_nonempty
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image Finset.univ ν Finset.univ_nonempty
  have hlower : ν j*R ≤ ∑t,K i t*ν t := by
    rw [←hrow i,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    calc ν j*K i t = K i t*ν j := mul_comm _ _
         _ ≤ K i t*ν t := mul_le_mul_of_nonneg_left (hmin t (Finset.mem_univ _)) (hK i t).le
  have hupper : (∑t,K t j*μ t) ≤ μ i*R := by
    rw [←hcol j,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro t _
    calc K t j*μ t ≤ K t j*μ i := mul_le_mul_of_nonneg_left (hmax t (Finset.mem_univ _)) (hK t j).le
         _ = μ i*K t j := mul_comm _ _
  have hbalance : (∑t,K i t*ν t)=ν j*R := by
    have ha := mul_le_mul_of_nonneg_left hlower (hμ i).le
    have hb := mul_le_mul_of_nonneg_left hupper (hν j).le
    rw [hleft] at ha
    rw [hright,←hcd] at hb
    have hh : μ i*(∑t,K i t*ν t)=μ i*(ν j*R) := by
      rw [hleft]
      nlinarith
    exact mul_left_cancel₀ (hμ i).ne' hh
  have hdiff : (∑t,K i t*(ν t-ν j))=0 := by
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,←Finset.sum_mul,hrow i,hbalance]
    ring
  have hn : ∀t∈(Finset.univ : Finset I),0≤K i t*(ν t-ν j) :=
    fun t _=>mul_nonneg (hK i t).le (sub_nonneg.mpr (hmin t (Finset.mem_univ _)))
  have hνconst : ∀t,ν t=ν j := by
    intro t
    have ht := (Finset.sum_eq_zero_iff_of_nonneg hn).mp hdiff t (Finset.mem_univ _)
    exact sub_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (hK i t).ne')
  have hsums (t : I) : (∑s,K t s*ν s)=ν j*R := by
    simp only [hνconst,←Finset.sum_mul,hrow]
    ring
  refine ⟨?_,fun a b=>(hνconst a).trans (hνconst b).symm⟩
  intro a b
  apply mul_right_cancel₀ (mul_pos (hν j) hR).ne'
  have ha := hleft a
  have hb := hleft b
  rw [hsums] at ha hb
  exact ha.trans hb.symm

end PlanarHom.PositiveKernelScalingRigidity
