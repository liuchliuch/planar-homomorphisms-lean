import PlanarHom.RectangularNormRigidity

/-! NEW degree-two permanent row norm identity and its equality case. These
are the exact finite numerical inequalities used to force disjoint supports. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
variable {I:Type} [Fintype I] [LinearOrder I]

theorem sum_symmetric_upper (f:I→I→ℝ) (hs:∀i j,f i j=f j i):
    (∑i,∑j,f i j)=2*(∑i,∑j,if i < j then f i j else 0)+(∑i,f i i):=by
  have hsplit:∀i j,f i j=(if i < j then f i j else 0)+(if j < i then f i j else 0)+(if i=j then f i j else 0):=by
    intro i j
    rcases lt_trichotomy i j with h|h|h
    · simp [h,not_lt_of_ge h.le,h.ne]
    · subst j
      simp
    · simp [h,not_lt_of_ge h.le,h.ne']
  calc
    _ = (∑i,∑j,if i < j then f i j else 0)+(∑i,∑j,if j < i then f i j else 0)+(∑i,∑j,if i=j then f i j else 0):=by
      simp_rw [←Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      exact hsplit i j
    _ = _:=by
      have he:(∑i,∑j,if j < i then f i j else 0)=(∑i,∑j,if i < j then f i j else 0):=by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        rw [hs j i]
      rw [he]
      simp only [Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,ite_true]
      ring

def pairPermanent (u v:I→ℝ) (p:I×I):ℝ:=if p.1 < p.2 then u p.1*v p.2+u p.2*v p.1 else 0

theorem pairPermanent_norm (u v:I→ℝ):
    (∑p:I×I,pairPermanent u v p^2)=
      (∑i,u i^2)*(∑i,v i^2)+(∑i,u i*v i)^2-2*(∑i,u i^2*v i^2):=by
  have hfull:(∑i,∑j,(u i*v j+u j*v i)^2)=
      2*((∑i,u i^2)*(∑i,v i^2))+2*(∑i,u i*v i)^2:=by
    calc
      _ = ∑i,∑j,(u i^2*v j^2+u j^2*v i^2+2*((u i*v i)*(u j*v j))):=by
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        ring
      _ = _:=by
        simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,pow_two]
        ring
  have hsym:∀i j,(u i*v j+u j*v i)^2=(u j*v i+u i*v j)^2:=by intros;ring
  have hupper:=sum_symmetric_upper (fun i j=>(u i*v j+u j*v i)^2) hsym
  have hdiag:(∑i,(u i*v i+u i*v i)^2)=4*(∑i,u i^2*v i^2):=by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hp:(∑p:I×I,pairPermanent u v p^2)=∑i,∑j,if i < j then (u i*v j+u j*v i)^2 else 0:=by
    simp only [Fintype.sum_prod_type,pairPermanent,ite_pow,zero_pow (by decide:2≠0)]
  rw [hdiag] at hupper
  rw [hp]
  linarith

theorem degree_two_saturation_disjoint (u v:I→ℝ) (r:I×I→ℝ)
    (hu:(∑i,u i^2)=1) (hv:(∑i,v i^2)=1) (huv:(∑i,u i*v i)=0)
    (hr:(∑p,r p^2)=1) (hmax:(∑p,(r p+pairPermanent u v p)^2)=4) :
    ∀i,u i*v i=0:=by
  have hn:=pairPermanent_norm u v
  rw [hu,hv,huv] at hn
  have hsum:0≤∑i,u i^2*v i^2:=Finset.sum_nonneg (fun i _=>mul_nonneg (sq_nonneg _) (sq_nonneg _))
  have hp:(∑p,pairPermanent u v p^2)≤1:=by nlinarith
  have he: (∑p,pairPermanent u v p^2)=1:=(unit_plus_short_max r (pairPermanent u v) hr hp hmax).1
  have hz:(∑i,u i^2*v i^2)=0:=by nlinarith
  intro i
  have hi:u i^2*v i^2=0:=(Finset.sum_eq_zero_iff_of_nonneg
    (fun j _=>mul_nonneg (sq_nonneg (u j)) (sq_nonneg (v j)))).mp hz i (Finset.mem_univ _)
  nlinarith [sq_nonneg (u i*v i)]

end PlanarHom.RectangularWalshConvolution
