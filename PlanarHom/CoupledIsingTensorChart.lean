import PlanarHom.CoupledIsingActualQuotient
import PlanarHom.CenteredLogStructuralConverse
import PlanarHom.InjectiveWeightedStructuralTransfer

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CoupledIsing
open BinaryCharacters Boolean Structures
variable {n m:ℕ}

def cubeEquiv (m:ℕ) : Space m≃Cube m := Equiv.piCongrRight (fun _=>bitEquiv)

def imageEquivSpace (a:Fin m→Space n) (ha:Function.Surjective (characterMap a)) : ImageSpace a≃Space m :=
  Equiv.ofBijective Subtype.val ⟨Subtype.val_injective,by
    intro z
    obtain ⟨x,hx⟩:=ha z
    exact ⟨⟨z,⟨x,hx⟩⟩,rfl⟩⟩

def imageCubeEquiv (a:Fin m→Space n) (ha:Function.Surjective (characterMap a)) : ImageSpace a≃Cube m :=
  (imageEquivSpace a ha).trans (cubeEquiv m)

theorem single_sign_exp (J:ℝ) (x y:F₂) :
    Real.exp (J*sign x*sign y)=Real.exp J*W (Real.exp (-2*J)) (bitEquiv x) (bitEquiv y) := by
  fin_cases x <;> fin_cases y <;>
    simp [sign,W,←Real.exp_add] <;> congr 1 <;> ring

theorem quotient_tensor (a:Fin m→Space n) (ha:Function.Surjective (characterMap a))
    (J:Fin m→ℝ) (x y:ImageSpace a) :
    quotientInteraction a J x y=Real.exp (∑r,J r)*
      tensor (fun r=>Real.exp (-2*J r)) (imageCubeEquiv a ha x) (imageCubeEquiv a ha y) := by
  change Real.exp (∑r,J r*sign (x.val r)*sign (y.val r))=_
  rw [Real.exp_sum]
  simp_rw [single_sign_exp]
  rw [Finset.prod_mul_distrib,←Real.exp_sum]
  rfl

theorem quotient_weightedClass_of_independent (a:Fin m→Space n)
    (ha:LinearIndependent F₂ a) (J:Fin m→ℝ) (hJ:∀r,J r≠0)
    (w:ImageSpace a→ℝ) (μ:ℝ) (hμ:0 < μ) (hw:∀x,w x=μ) :
    WeightedClass (quotientInteraction a J) w := by
  have hsurj:Function.Surjective (characterMap a):=(map_surjective_iff_independent a).mpr ha
  apply AllowedWeightedBlock.weightedClass
  refine CenteredLogStructural.scaled_tensor_allowedBlock _ _ (imageCubeEquiv a hsurj)
    (Real.exp (∑r,J r)) μ (Real.exp_pos _) hμ (fun r=>Real.exp (-2*J r)) ?_
    (quotient_tensor a hsurj J) hw
  intro r
  refine ⟨Real.exp_pos _,?_⟩
  intro h
  have hz: -2*J r=0:=Real.exp_injective (by simpa only [Real.exp_zero] using h)
  exact hJ r ((mul_eq_zero.mp hz).resolve_left (by norm_num))

end PlanarHom.CoupledIsing
