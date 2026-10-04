import PlanarHom.RectangularRowConvolution
import PlanarHom.RectangularDegreeIndexSums
import PlanarHom.RectangularDegreeTwoNorm

/-! NEW degree-one convolution norms in the actual Boolean Fourier index set. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem degree_unitBit (i:Fin d):Boolean.degree (unitBit i)=1:=by
  rw [degree_eq_support_card,support_unitBit,Finset.card_singleton]

theorem rowConvolution_linear (u v:Cube d→ℝ)
    (hu:∀S,Boolean.degree S≠1→u S=0) (T:Cube d):
    rowConvolution u v T=∑i:Fin d,u (unitBit i)*v (xor T (unitBit i)):=by
  apply sum_degree_one
  intro S hs
  rw [hu S hs,zero_mul]

theorem pair_xor_unit_degree (j k i:Fin d) (hjk:j≠k):
    Boolean.degree (xor (pairBits j k) (unitBit i))=1↔i=j ∨ i=k:=by
  constructor
  · intro hd
    have hm:Boolean.degree (unitBit i)+Boolean.degree (xor (pairBits j k) (unitBit i))=
        Boolean.degree (pairBits j k):=by rw [degree_unitBit,hd,pairBits_degree j k hjk]
    have hs:bitSupport (unitBit i)⊆bitSupport (pairBits j k):=(minimal_split_iff _ _).mp hm
    have hi:i∈bitSupport (pairBits j k):=hs (by rw [support_unitBit];simp)
    simpa only [support_pairBits,Finset.mem_insert,Finset.mem_singleton] using hi
  · rintro (hi|hi)
    · subst i
      rw [pairBits_xor_left j k hjk,degree_unitBit]
    · subst i
      rw [pairBits_xor_right j k hjk,degree_unitBit]

theorem rowConvolution_pair (u v:Cube d→ℝ)
    (hu:∀S,Boolean.degree S≠1→u S=0) (hv:∀S,Boolean.degree S≠1→v S=0)
    (j k:Fin d) (hjk:j≠k):
    rowConvolution u v (pairBits j k)=u (unitBit j)*v (unitBit k)+u (unitBit k)*v (unitBit j):=by
  rw [rowConvolution_linear u v hu]
  have hs:(∑i∈({j,k}:Finset (Fin d)),u (unitBit i)*v (xor (pairBits j k) (unitBit i)))=
      ∑i:Fin d,u (unitBit i)*v (xor (pairBits j k) (unitBit i)):=by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro i _ hi
    have hn:¬(i=j ∨ i=k):=by simpa only [Finset.mem_insert,Finset.mem_singleton] using hi
    have hd:Boolean.degree (xor (pairBits j k) (unitBit i))≠1:=fun h=>hn ((pair_xor_unit_degree j k i hjk).mp h)
    rw [hv _ hd,mul_zero]
  rw [←hs,Finset.sum_pair hjk,pairBits_xor_left j k hjk,pairBits_xor_right j k hjk]

theorem rowConvolution_linear_support (u v:Cube d→ℝ)
    (hu:∀S,Boolean.degree S≠1→u S=0) (hv:∀S,Boolean.degree S≠1→v S=0)
    (hdot:(∑i:Fin d,u (unitBit i)*v (unitBit i))=0)
    (T:Cube d) (hT:Boolean.degree T≠2):rowConvolution u v T=0:=by
  rw [rowConvolution_linear u v hu]
  by_cases ht:T=(fun _=>false)
  · subst T
    simpa only [xor_zero_left] using hdot
  · apply Finset.sum_eq_zero
    intro i _
    have hzero:Boolean.degree T≠0:=fun h=>ht ((degree_zero_iff T).mp h)
    have hx:xor (unitBit i) (xor T (unitBit i))=T:=by funext j;simp [Boolean.xor,Bool.xor_comm,Bool.xor_left_comm]
    have hd:Boolean.degree (xor T (unitBit i))≠1:=by
      intro h
      have hcount:=degree_xor_add (unitBit i) (xor T (unitBit i))
      rw [degree_unitBit,h,hx] at hcount
      omega
    rw [hv _ hd,mul_zero]

theorem linear_convolution_norm (u v:Cube d→ℝ)
    (hu:∀S,Boolean.degree S≠1→u S=0) (hv:∀S,Boolean.degree S≠1→v S=0)
    (hdot:(∑i:Fin d,u (unitBit i)*v (unitBit i))=0):
    (∑T:Cube d,(rowConvolution u v T)^2)=
      (∑i:Fin d,u (unitBit i)^2)*(∑i:Fin d,v (unitBit i)^2)-
        2*(∑i:Fin d,u (unitBit i)^2*v (unitBit i)^2):=by
  rw [sum_degree_two (fun T=>(rowConvolution u v T)^2)
    (by intro T hT;dsimp only;rw [rowConvolution_linear_support u v hu hv hdot T hT];norm_num)]
  have hp:(∑p:Fin d×Fin d,if p.1 < p.2 then (rowConvolution u v (pairBits p.1 p.2))^2 else 0)=
      ∑p:Fin d×Fin d,pairPermanent (fun i=>u (unitBit i)) (fun i=>v (unitBit i)) p^2:=by
    apply Finset.sum_congr rfl
    intro p _
    by_cases h:p.1 < p.2
    · simp only [h,if_true,rowConvolution_pair u v hu hv p.1 p.2 h.ne,pairPermanent]
    · simp only [h,if_false,pairPermanent,zero_pow (by decide:2≠0)]
  rw [hp,pairPermanent_norm,hdot]
  ring

end PlanarHom.RectangularWalshConvolution
