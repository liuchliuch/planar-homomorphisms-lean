import PlanarHom.SurfaceFourierCalibration
import PlanarHom.SurfaceCycleEdgeSets

/-! NEW exact edge-weight character twists from literal F2 coordinate maps.
Only signs multiply the existing field weights; no square roots or additional
orientation search are used. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceBooleanGauss
variable {K : Type*} [CommRing K]

def toBits {d : ℕ} (x : Fin d→ZMod 2) : Bits d := fun i=>decide (x i=1)
def ofBits {d : ℕ} (x : Bits d) : Fin d→ZMod 2 := fun i=>if x i then 1 else 0

@[simp] theorem toBits_ofBits {d : ℕ} (x : Bits d) : toBits (ofBits x)=x := by
  funext i
  cases hx:x i <;> simp [toBits,ofBits,hx]

@[simp] theorem ofBits_toBits {d : ℕ} (x : Fin d→ZMod 2) : ofBits (toBits x)=x := by
  funext i
  have h (z : ZMod 2) : (if z=1 then (1:ZMod 2) else 0)=z := by fin_cases z <;> decide
  simpa only [ofBits,toBits,decide_eq_true_eq] using h (x i)

def bitVectorEquiv (d : ℕ) : (Fin d→ZMod 2)≃Bits d :=
  ⟨toBits,ofBits,ofBits_toBits,toBits_ofBits⟩

def characterF2 {d : ℕ} (u : Bits d) (x : Fin d→ZMod 2) : K := character u (toBits x)

theorem bitSign_add (u : Bool) (x y : ZMod 2) :
    bitSign (K:=K) u (decide (x+y=1))=bitSign u (decide (x=1))*bitSign u (decide (y=1)) := by
  have ht : (2:ZMod 2)≠1 := by decide
  cases u <;> fin_cases x <;> fin_cases y <;> norm_num [bitSign,ht]

@[simp] theorem characterF2_zero {d : ℕ} (u : Bits d) : characterF2 (K:=K) u 0=1 := by
  simp [characterF2,character,toBits,bitSign]

theorem characterF2_add {d : ℕ} (u : Bits d) (x y : Fin d→ZMod 2) :
    characterF2 (K:=K) u (x+y)=characterF2 u x*characterF2 u y := by
  simp only [characterF2,character,toBits,Pi.add_apply,←Finset.prod_mul_distrib,bitSign_add]

theorem characterF2_mul_self {d : ℕ} (u : Bits d) (x : Fin d→ZMod 2) :
    characterF2 (K:=K) u x*characterF2 u x=1 := character_mul_self _ _

theorem characterF2_sum {d : ℕ} {I : Type*} (u : Bits d) (s : Finset I) (f : I→Fin d→ZMod 2) :
    characterF2 (K:=K) u (∑i∈s,f i)=∏i∈s,characterF2 u (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => rw [Finset.sum_insert ha,Finset.prod_insert ha,characterF2_add,ih]

end PlanarHom.SurfaceBooleanGauss
namespace PlanarHom.MultiGraph
variable {E : Type*} [Fintype E]

theorem edgeIndicator_eq_sum_single (M : Finset E) :
    edgeIndicator M=∑e∈M,Pi.single e (1:ZMod 2) := by
  funext e
  simp [edgeIndicator,Pi.single_apply,eq_comm]

end PlanarHom.MultiGraph
namespace PlanarHom.SurfaceBooleanGauss
open MultiGraph
variable {K E : Type*} [CommRing K] [Fintype E] {d : ℕ}

theorem character_indicator_product (L : (E→ZMod 2)→ₗ[ZMod 2](Fin d→ZMod 2))
    (u : Bits d) (M : Finset E) :
    characterF2 (K:=K) u (L (edgeIndicator M))=
      ∏e∈M,characterF2 u (L (Pi.single e 1)) := by
  rw [edgeIndicator_eq_sum_single,map_sum]
  exact characterF2_sum u M _

def twistWeights (L : (E→ZMod 2)→ₗ[ZMod 2](Fin d→ZMod 2)) (u : Bits d) (w : E→K) : E→K :=
  fun e=>w e*characterF2 u (L (Pi.single e 1))

theorem prod_twistWeights (L : (E→ZMod 2)→ₗ[ZMod 2](Fin d→ZMod 2))
    (u : Bits d) (w : E→K) (M : Finset E) :
    (∏e∈M,twistWeights L u w e)=(∏e∈M,w e)*characterF2 u (L (edgeIndicator M)) := by
  rw [character_indicator_product]
  exact Finset.prod_mul_distrib

end PlanarHom.SurfaceBooleanGauss
