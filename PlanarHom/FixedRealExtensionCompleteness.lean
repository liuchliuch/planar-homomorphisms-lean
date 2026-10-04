import PlanarHom.FixedRealExtensionSemantics

/-! Existence of compatible shared-denominator presentations and fixed
multiplication tables. These are finite constant choices, not runtime subfield
recognition or a claimed polynomial-time presentation-discovery algorithm. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.DensePolynomial

theorem exists_common_denominator {I:Type} [Fintype I] (n:ℕ) (x:I→RationalFunction n) :
    ∃d:Code n,∃p:I→Code n,interpret n d≠0 ∧ ∀i,fractionValue n (p i,d)=x i := by
  let c:I→FractionCode n:=fun i=>Classical.choose (fraction_complete n (x i))
  have hc:∀i,FractionValid n (c i) ∧ fractionValue n (c i)=x i:=
    fun i=>Classical.choose_spec (fraction_complete n (x i))
  let D:Poly n:=∏i,interpret n (c i).2
  have hD:D≠0:=Finset.prod_ne_zero_iff.mpr (fun i _=>(hc i).1)
  obtain ⟨d,hd⟩:=interpret_surjective n D
  let P:I→Poly n:=fun i=>interpret n (c i).1 * ∏j∈Finset.univ.erase i,interpret n (c j).2
  let p:I→Code n:=fun i=>Classical.choose (interpret_surjective n (P i))
  have hp:∀i,interpret n (p i)=P i:=fun i=>Classical.choose_spec (interpret_surjective n (P i))
  refine ⟨d,p,by rwa [hd],?_⟩
  intro i
  have hprod : D=interpret n (c i).2 * ∏j∈Finset.univ.erase i,interpret n (c j).2 := by
    exact (Finset.mul_prod_erase Finset.univ (fun j=>interpret n (c j).2) (Finset.mem_univ i)).symm
  have ho : (∏j∈Finset.univ.erase i,interpret n (c j).2)≠0 :=
    Finset.prod_ne_zero_iff.mpr (fun j _=>(hc j).1)
  have hoF : algebraMap (Poly n) (RationalFunction n)
      (∏j∈Finset.univ.erase i,interpret n (c j).2)≠0 :=
    fun h=>ho ((IsFractionRing.to_map_eq_zero_iff).mp h)
  calc
    fractionValue n (p i,d)=fractionValue n (c i) := by
      simp only [fractionValue,hp,hd,P,hprod,map_mul]
      exact mul_div_mul_right _ _ hoF
    _ =x i:=(hc i).2

end PlanarHom.DensePolynomial
namespace PlanarHom.FixedRealExtension
open DensePolynomial
variable {n e:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]

theorem exists_multiplicationTable (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    ∃T:MultiplicationTable n e,T.Realizes basis := by
  obtain ⟨d,p,hd,hp⟩:=DensePolynomial.exists_common_denominator n
    (fun v:Fin e×Fin e×Fin e=>basis.equivFun (basis v.1*basis v.2.1) v.2.2)
  exact ⟨⟨d,fun i j k=>p (i,j,k),hd⟩,fun i j k=>hp (i,j,k)⟩

def multiplicationTable (basis:Module.Basis (Fin e) (RationalFunction n) K) : MultiplicationTable n e :=
  Classical.choose (exists_multiplicationTable basis)

theorem multiplicationTable_realizes (basis:Module.Basis (Fin e) (RationalFunction n) K) :
    (multiplicationTable basis).Realizes basis := Classical.choose_spec (exists_multiplicationTable basis)

theorem value_complete (basis:Module.Basis (Fin e) (RationalFunction n) K) (x:K) :
    ∃a:Code n e,Valid n a ∧ value basis a=x := by
  obtain ⟨d,p,hd,hp⟩:=DensePolynomial.exists_common_denominator n (basis.equivFun x)
  refine ⟨(p,d),hd,?_⟩
  have he:coordinates n (p,d)=basis.equivFun x:=funext hp
  rw [value,he,basis.equivFun.symm_apply_apply]

end PlanarHom.FixedRealExtension
