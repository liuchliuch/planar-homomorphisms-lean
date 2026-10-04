import PlanarHom.RectangularSubsetCoefficients

/-! NEW exact singleton and unordered-pair indexing of Fourier degree sums. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem unitBit_injective:Function.Injective (unitBit:Fin d→Cube d):=by
  intro i j h
  have hs:=congrArg bitSupport h
  simpa only [support_unitBit,Finset.singleton_inj] using hs

theorem degree_one_iff (S:Cube d):Boolean.degree S=1↔∃i:Fin d,S=unitBit i:=by
  rw [degree_eq_support_card,Finset.card_eq_one]
  constructor
  · rintro ⟨i,hi⟩
    refine ⟨i,?_⟩
    apply (bitSetEquiv d).injective
    change bitSupport S=bitSupport (unitBit i)
    simpa only [support_unitBit] using hi
  · rintro ⟨i,rfl⟩
    exact ⟨i,support_unitBit i⟩

theorem sum_degree_one {R:Type} [AddCommMonoid R] (f:Cube d→R)
    (hz:∀S,Boolean.degree S≠1→f S=0):
    (∑S:Cube d,f S)=∑i:Fin d,f (unitBit i):=by
  have hset:Finset.univ.filter (fun S:Cube d=>Boolean.degree S=1)=Finset.univ.image unitBit:=by
    ext S
    constructor
    · intro h
      obtain ⟨i,hi⟩:=(degree_one_iff S).mp (Finset.mem_filter.mp h).2
      exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,hi.symm⟩
    · intro h
      obtain ⟨i,_,hi⟩:=Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(degree_one_iff S).mpr ⟨i,hi.symm⟩⟩
  calc
    _=∑S∈Finset.univ.filter (fun S:Cube d=>Boolean.degree S=1),f S:=by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hs:Boolean.degree S=1 <;> simp [hs,hz S]
    _ = _:=by
      rw [hset,Finset.sum_image (fun i _ j _ h=>unitBit_injective h)]

theorem pairBits_ordered_injective (p q:Fin d×Fin d) (hp:p.1 < p.2) (hq:q.1 < q.2)
    (h:pairBits p.1 p.2=pairBits q.1 q.2):p=q:=by
  have hs:=congrArg bitSupport h
  simp only [support_pairBits] at hs
  have hp1:p.1=q.1 ∨ p.1=q.2:=by
    have hi:p.1∈({q.1,q.2}:Finset (Fin d)):=hs ▸ (by simp)
    simpa using hi
  have hp2:p.2=q.1 ∨ p.2=q.2:=by
    have hi:p.2∈({q.1,q.2}:Finset (Fin d)):=hs ▸ (by simp)
    simpa using hi
  apply Prod.ext <;> omega

theorem degree_two_iff (S:Cube d):Boolean.degree S=2↔∃i k:Fin d,i < k ∧ S=pairBits i k:=by
  rw [degree_eq_support_card,Finset.card_eq_two]
  constructor
  · rintro ⟨i,k,hik,hs⟩
    have he:S=pairBits i k:=by
      apply (bitSetEquiv d).injective
      change bitSupport S=bitSupport (pairBits i k)
      simpa only [support_pairBits] using hs
    rcases lt_or_gt_of_ne hik with h|h
    · exact ⟨i,k,h,he⟩
    · refine ⟨k,i,h,?_⟩
      simpa only [pairBits,Finset.pair_comm] using he
  · rintro ⟨i,k,hik,rfl⟩
    exact ⟨i,k,hik.ne,support_pairBits i k⟩

theorem sum_degree_two {R:Type} [AddCommMonoid R] (f:Cube d→R)
    (hz:∀S,Boolean.degree S≠2→f S=0):
    (∑S:Cube d,f S)=∑p:Fin d×Fin d,if p.1 < p.2 then f (pairBits p.1 p.2) else 0:=by
  let pairs:=Finset.univ.filter (fun p:Fin d×Fin d=>p.1 < p.2)
  have hset:Finset.univ.filter (fun S:Cube d=>Boolean.degree S=2)=pairs.image (fun p=>pairBits p.1 p.2):=by
    ext S
    constructor
    · intro h
      obtain ⟨i,k,hik,he⟩:=(degree_two_iff S).mp (Finset.mem_filter.mp h).2
      exact Finset.mem_image.mpr ⟨(i,k),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hik⟩,he.symm⟩
    · intro h
      obtain ⟨p,hp,he⟩:=Finset.mem_image.mp h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(degree_two_iff S).mpr
        ⟨p.1,p.2,(Finset.mem_filter.mp hp).2,he.symm⟩⟩
  calc
    _=∑S∈Finset.univ.filter (fun S:Cube d=>Boolean.degree S=2),f S:=by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro S _
      by_cases hs:Boolean.degree S=2 <;> simp [hs,hz S]
    _ = ∑p∈pairs,f (pairBits p.1 p.2):=by
      rw [hset,Finset.sum_image]
      intro p hp q hq he
      exact pairBits_ordered_injective p q (Finset.mem_filter.mp hp).2 (Finset.mem_filter.mp hq).2 he
    _ = _:=by dsimp only [pairs];rw [Finset.sum_filter]

end PlanarHom.RectangularWalshConvolution
