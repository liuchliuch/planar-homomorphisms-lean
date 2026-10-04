import PlanarHom.FinitePermutationFiberCount
import PlanarHom.FinitePermutationCycleTransport

/-! NEW exact cycle count of a disjoint dependent family of permutations. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FinitePermutationCycles
variable {I : Type} {D : I→Type} [Fintype I] [∀i,Fintype (D i)]

 def sigmaPerm (P : ∀i,Equiv.Perm (D i)) : Equiv.Perm (Sigma D) := Equiv.sigmaCongrRight P

 def sigmaFiber (i : I) : {d : Sigma D // d.1=i}≃D i where
  toFun d:=d.property ▸ d.val.2
  invFun d:=⟨⟨i,d⟩,rfl⟩
  left_inv d:=by rcases d with ⟨⟨j,d⟩,h⟩; dsimp only at h; subst j; rfl
  right_inv d:=rfl

 theorem count_sigmaPerm (P : ∀i,Equiv.Perm (D i)) : count (sigmaPerm P)=∑i,count (P i) := by
  rw [count_eq_sum_fibers (sigmaPerm P) Sigma.fst (fun _=>rfl)]
  apply Finset.sum_congr rfl
  intro i _
  apply count_semiconj _ _ (sigmaFiber i)
  rintro ⟨⟨j,d⟩,h⟩
  dsimp only at h
  subst j
  rfl

end PlanarHom.FinitePermutationCycles
