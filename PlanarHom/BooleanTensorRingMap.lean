import PlanarHom.BooleanTensorPartitionMoments
import PlanarHom.MixedEvaluationFieldMap

/-! NEW exact ring-homomorphism transport into the represented radical algebra.
Original companion matrices, unaries, weights and every occurrence are retained. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.BooleanTensorRingMap
open BooleanTensorSpectral BooleanTensorPartitionMoments Complexity Complexity.MixedCode
variable {K R : Type} [CommRing K] [CommRing R] {d bt ut : ℕ}

theorem block_map (φ : K→+*R) (c a u : K) :
    (block c a u).map φ = block (φ c) (φ a) (φ u) := by
  ext i j
  cases i <;> cases j <;>
    simp [block,traceless,Matrix.map_apply,Matrix.add_apply,Matrix.smul_apply]

theorem tensor_map (φ : K→+*R) (A : Fin d→Matrix Bool Bool K) :
    (tensor A).map φ = tensor (fun i=>(A i).map φ) := by
  ext z w
  exact map_prod φ _ _

theorem tensor_blocks_map (φ : K→+*R) (c a u : Fin d→K) :
    (tensor (fun i=>block (c i) (a i) (u i))).map φ =
      tensor (fun i=>block (φ (c i)) (φ (a i)) (φ (u i))) := by
  rw [tensor_map]
  simp only [block_map]

theorem tensor_power_map (φ : K→+*R) (c a u : Fin d→K) (n : ℕ) :
    ((tensor (fun i=>block (c i) (a i) (u i)))^n).map φ =
      (tensor (fun i=>block (φ (c i)) (φ (a i)) (φ (u i))))^n := by
  have h:=map_pow φ.mapMatrix (tensor (fun i=>block (c i) (a i) (u i))) n
  change ((tensor (fun i=>block (c i) (a i) (u i)))^n).map φ =
    ((tensor (fun i=>block (c i) (a i) (u i))).map φ)^n at h
  simpa only [tensor_blocks_map] using h

theorem tensor_retained_map (φ : K→+*R) (c a u : Fin d→K) (S : Finset (Fin d)) :
    (tensor (fun i=>if i∈S then block (c i) (a i) (u i) else 1)).map φ =
      tensor (fun i=>if i∈S then block (φ (c i)) (φ (a i)) (φ (u i)) else 1) := by
  rw [tensor_map]
  congr 1
  funext i
  by_cases hi:i∈S
  · simp only [hi,if_true,block_map]
  · simp [hi]

theorem mapped_evaluate_replace (φ : K→+*R) (g : MixedCode) (hg:g.Valid bt ut)
    (selected : Fin bt) (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K)
    (U : Fin ut→(Fin d→Bool)→K) (w : (Fin d→Bool)→K)
    (A : Matrix (Fin d→Bool) (Fin d→Bool) K) :
    φ (g.evaluate hg (replace M selected A) U w) =
      g.evaluate hg (replace (fun l=>(M l).map φ) selected (A.map φ))
        (fun l i=>φ (U l i)) (fun i=>φ (w i)) := by
  rw [map_evaluate]
  congr 1
  funext l i j
  by_cases h:l=selected <;> simp [replace,h]

end PlanarHom.BooleanTensorRingMap
