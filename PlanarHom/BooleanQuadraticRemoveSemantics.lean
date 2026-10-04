import PlanarHom.BooleanQuadraticPivotSemantics
import PlanarHom.BooleanQuadraticClearing

/-! NEW exact singleton elimination and the actual pivot-search alternatives. -/
namespace PlanarHom.BooleanQuadratic
open scoped BigOperators

 theorem gauss_remove {K : Type*} [CommRing K] {n : ℕ}
    (q : Data) (hn : dimension q=n) (i : Fin n)
    (hp : ∀k:Fin n,k≠i→cross q i.val k.val=false) :
    gauss (K:=K) n q=if linear q i.val then 0 else gauss n (remove q i.val) := by
  classical
  let t : Finset (Fin n):=Finset.univ.erase i
  let l : Fin n→F₂:=fun k=>bit (rawLinear q k.val)
  let m : Fin n→Fin n→F₂:=fun k r=>bit (entry q k.val r.val)
  let C := fun z=>form t (bit q.1) l m (extendSingle i z)
  have hC (x:Fin n→F₂) : C (fun k=>x k.val)=form t (bit q.1) l m x :=
    form_congr_on t _ _ _ _ _ (fun k hk=>extendSingle_restrict Finset.univ i x k hk)
  have hphase (x:Fin n→F₂) : phase n q x=C (fun k=>x k.val)+bit (linear q i.val)*x i := by
    rw [hC]
    unfold phase
    rw [form_extract Finset.univ i (Finset.mem_univ i)]
    have hz : (∑k∈Finset.univ.erase i,
        (bit (entry q i.val k.val)+bit (entry q k.val i.val))*x i*x k)=0 := by
      apply Finset.sum_eq_zero
      intro k hk
      rw [←bit_xor]
      change bit (cross q i.val k.val)*x i*x k=0
      rw [hp k (Finset.mem_erase.mp hk).1,bit_false,zero_mul,zero_mul]
    rw [hz,add_zero]
    simp only [t,l,m,linear,rawLinear,bit_xor]
  have hres (x:Fin n→F₂) : phase n (remove q i.val) x=C (fun k=>x k.val) := by
    rw [hC,phase_remove q hn i]
  unfold gauss
  simp_rw [hphase,hres]
  rw [singleton_elimination]
  cases h:linear q i.val <;> simp [h,bit]

 theorem partner_some (q : Data) (i j : ℕ) (h : partner q i=some j) :
    i<j ∧ j<dimension q ∧ cross q i j=true := by
  have hm:=List.mem_of_find?_eq_some h
  have hp:=List.find?_some h
  simp only [List.mem_range] at hm
  simp only [Bool.and_eq_true,decide_eq_true_eq] at hp
  exact ⟨hp.1,hm,hp.2⟩

 theorem partner_none_cross (q : Data) (i : ℕ) (h : partner q i=none)
    (hl : ∀ k < i,Cleared q k) : ∀ k < dimension q,k≠i→cross q i k=false := by
  intro k hk hki
  by_cases hik:i<k
  · have hp:=List.find?_eq_none.mp h k (List.mem_range.mpr hk)
    simpa [hik] using hp
  · have hc:=hl k (by omega)
    simp [cross,(hc.2 i).1,(hc.2 i).2]

end PlanarHom.BooleanQuadratic
