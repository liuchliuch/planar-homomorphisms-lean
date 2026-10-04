import PlanarHom.CoupledIsingAlgebraicDichotomy

/-! The finite-set presentation in Corollary 12.6, including literal binary
dot-product signs. Enumeration is only a bijective fixed index choice. -/
noncomputable section
set_option maxHeartbeats 800000
open Classical
open scoped BigOperators
namespace PlanarHom.CoupledIsing
open BinaryCharacters Structures
variable {n:ℕ}

theorem sign_eq_neg_one_pow (x:F₂) : sign x=(-1:ℝ)^x.val := by
  fin_cases x <;> norm_num [sign,show (1:F₂).val=1 by decide]

theorem interaction_formula {m:ℕ} (a:Fin m→Space n) (J:Fin m→ℝ) (x y:Space n) :
    interaction a J x y=Real.exp (∑r,J r*(-1:ℝ)^(∑i,a r i*x i).val*(-1:ℝ)^(∑i,a r i*y i).val) := by
  simp only [interaction,BinaryCharacters.interaction,kernel,character,functional,LinearMap.coe_mk,
    AddHom.coe_mk,sign_eq_neg_one_pow]

def setLabels (A:Finset (Space n)) : Fin (Fintype.card ↥A)→Space n :=
  fun r=>((Fintype.equivFin ↥A).symm r).val

def setCouplings (A:Finset (Space n)) (J:Space n→ℝ) : Fin (Fintype.card ↥A)→ℝ :=
  fun r=>J (setLabels A r)

theorem setLabels_injective (A:Finset (Space n)) : Function.Injective (setLabels A) :=
  Subtype.val_injective.comp (Fintype.equivFin ↥A).symm.injective

theorem setLabels_nonzero (A:Finset (Space n)) (hA:(0:Space n)∉A) : ∀r,setLabels A r≠0 := by
  intro r h
  have hm:=((Fintype.equivFin ↥A).symm r).property
  exact hA (by simpa only [←h] using hm)

theorem setLabels_independent_iff (A:Finset (Space n)) :
    LinearIndependent F₂ (setLabels A) ↔ LinearIndependent F₂ (fun a:↥A=>a.val) :=
  linearIndependent_equiv' (Fintype.equivFin ↥A).symm rfl

theorem set_interaction_formula (A:Finset (Space n)) (J:Space n→ℝ) (x y:Space n) :
    interaction (setLabels A) (setCouplings A J) x y=
      Real.exp (∑a:↥A,J a.val*(-1:ℝ)^(∑i,a.val i*x i).val*(-1:ℝ)^(∑i,a.val i*y i).val) := by
  rw [interaction_formula]
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin ↥A).symm _ _ (fun _=>rfl)

theorem finite_set_weighted_class_iff (A:Finset (Space n)) (hA:(0:Space n)∉A)
    (J:Space n→ℝ) (hJ:∀a∈A,J a≠0) (w:Space n→ℝ) (hw:∀x,0 < w x) :
    PositiveVertexWeightClass (interaction (setLabels A) (setCouplings A J)) w
      (symmetric (setLabels A) (setCouplings A J)) ↔
    LinearIndependent F₂ (fun a:↥A=>a.val) ∧
      ∃μ:ℝ,0 < μ ∧ ∀z,aggregatedWeight (setLabels A) w z=μ := by
  rw [weighted_class_iff (setLabels A) (setLabels_injective A) (setLabels_nonzero A hA)
    (setCouplings A J) (fun r=>hJ _ ((Fintype.equivFin ↥A).symm r).property) w hw]
  rw [setLabels_independent_iff]

theorem image_card {m:ℕ} (a:Fin m→Space n) :
    Fintype.card (ImageSpace a)=2^Matrix.rank a := by
  rw [Module.card_eq_pow_finrank (K:=F₂),ZMod.card]
  rfl

end PlanarHom.CoupledIsing
