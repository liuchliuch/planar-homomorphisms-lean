import PlanarHom.PlanarityLRContourEventOrder
import PlanarHom.OrderedPortIntervals

/-! NEW finite-cycle adjacency excludes alternating port pairs once the actual
cycle keys are proved increasing from its start. -/
noncomputable section
namespace PlanarHom.OrderedCycleAdjacentPorts
variable {A B : Type} [Finite A] [LinearOrder B]

 theorem exists_index (P : Equiv.Perm A) (s x : A) (hx : P.SameCycle s x) :
    ∃i,i<Function.minimalPeriod P s ∧ P^[i] s=x := by
  obtain ⟨n,hn⟩:=hx.exists_nat_pow_eq
  have hp:=Function.minimalPeriod_pos_of_mem_periodicPts (P.injective.mem_periodicPts s)
  refine ⟨n%Function.minimalPeriod P s,Nat.mod_lt _ hp,?_⟩
  rw [Function.iterate_mod_minimalPeriod_eq,Equiv.Perm.iterate_eq_pow]
  exact hn

 theorem outside_adjacent (P : Equiv.Perm A) (s : A) (key : A→B)
    (hstrict : ∀i j,i<j→j<Function.minimalPeriod P s→key (P^[i] s)<key (P^[j] s))
    {x y z : A} (hx : P.SameCycle s x) (hz : P.SameCycle s z)
    (hnext : P x=y) (hxy : key x<key y) (hzx : z≠x) (hzy : z≠y) :
    key z<key x ∨ key y<key z := by
  obtain ⟨i,hi,hix⟩:=exists_index P s x hx
  obtain ⟨j,hj,hjz⟩:=exists_index P s z hz
  have hiy : P^[i+1] s=y:=by rw [Function.iterate_succ_apply',hix,hnext]
  have hinext:i+1<Function.minimalPeriod P s := by
    by_contra hn
    have heq:i+1=Function.minimalPeriod P s:=by omega
    have hys:y=s:=by rw [heq,Function.iterate_minimalPeriod] at hiy; exact hiy.symm
    by_cases hi0:i=0
    · have hxs:x=s:=by simpa only [hi0,Function.iterate_zero_apply] using hix.symm
      rw [hxs,hys] at hxy
      exact (lt_irrefl _ hxy).elim
    · have hh:=hstrict 0 i (by omega) hi
      simp only [Function.iterate_zero_apply,hix] at hh
      rw [hys] at hxy
      exact (lt_asymm hxy hh).elim
  by_cases hji : j < i
  · exact Or.inl (by simpa only [hjz,hix] using hstrict j i hji hi)
  · have hne:j≠i:=by intro h; subst j; exact hzx (hjz.symm.trans hix)
    have hne':j≠i+1:=by intro h; rw [h,hiy] at hjz; exact hzy hjz.symm
    exact Or.inr (by simpa only [hjz,hiy] using hstrict (i+1) j (by omega) hj)

 theorem noncrossing_of_outside {x y u v : B} (hxy : x<y)
    (hu : u<x ∨ y<u) (hv : v<x ∨ y<v) : PortNoncrossing x y u v := by
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact (portNoncrossing_separated hu (hu.trans hxy) hv (hv.trans hxy)).symm
  · exact portNoncrossing_inside hu (hu.trans hxy) (hxy.trans hv) hv
  · exact (portNoncrossing_inside hv (hv.trans hxy) (hxy.trans hu) hu).swap_right
  · exact portNoncrossing_separated (hxy.trans hu) (hxy.trans hv) hu hv

end PlanarHom.OrderedCycleAdjacentPorts
