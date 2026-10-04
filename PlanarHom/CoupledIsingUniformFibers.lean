import PlanarHom.CoupledIsingStructuralClassification
import Mathlib.GroupTheory.Coset.Basic
import Mathlib.FieldTheory.Finiteness

noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.CoupledIsing
open BinaryCharacters Structures
variable {n m:ℕ}

def fiberEquivKernel (a:Fin m→Space n) (z:ImageSpace a) :
    {x//toImage a x=z}≃LinearMap.ker (toImage a) :=
  AddMonoidHom.fiberEquivKerOfSurjective (f:=(toImage a).toAddMonoidHom) (toImage_surjective a) z

theorem kernel_finrank (a:Fin m→Space n) :
    Module.finrank F₂ (LinearMap.ker (toImage a))=n-Matrix.rank a := by
  have h:=(toImage a).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (toImage_surjective a),finrank_top] at h
  have hn:Module.finrank F₂ (Space n)=n:=by simp [Space]
  rw [hn] at h
  change Matrix.rank a+Module.finrank F₂ (LinearMap.ker (toImage a))=n at h
  omega

theorem fiber_card (a:Fin m→Space n) (z:ImageSpace a) :
    Fintype.card {x//toImage a x=z}=2^(n-Matrix.rank a) := by
  rw [Fintype.card_congr (fiberEquivKernel a z),Module.card_eq_pow_finrank (K:=F₂),kernel_finrank]
  rw [ZMod.card]

theorem unit_aggregatedWeight (a:Fin m→Space n) (z:ImageSpace a) :
    aggregatedWeight a (fun _=>1) z=(2:ℝ)^(n-Matrix.rank a) := by
  simp only [aggregatedWeight,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one]
  rw [fiber_card,Nat.cast_pow,Nat.cast_ofNat]

theorem unit_weighted_class_iff (a:Fin m→Space n) (ha:Function.Injective a)
    (hn:∀r,a r≠0) (J:Fin m→ℝ) (hJ:∀r,J r≠0) :
    PositiveVertexWeightClass (interaction a J) (fun _=>1) (symmetric a J) ↔ LinearIndependent F₂ a := by
  rw [weighted_class_iff a ha hn J hJ (fun _=>1) (fun _=>zero_lt_one)]
  constructor
  · exact And.left
  · intro h
    exact ⟨h,(2:ℝ)^(n-Matrix.rank a),by positivity,unit_aggregatedWeight a⟩

end PlanarHom.CoupledIsing
