import PlanarHom.HammingPottsFieldFamily
import PlanarHom.Tensor
import PlanarHom.FullLogarithmicProductIdentities

/-! NEW literal finite-color tensor partition identity and selected clique-size
Potts factorization. Loops, parallel occurrences and isolates are all retained. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.HammingPottsTensorPartition
open HammingKernelTensor HammingPottsProductIdentities HammingPottsFieldFamily

variable {V E I : Type*} [Fintype V] [Fintype E] [Fintype I] [DecidableEq I]
variable {A : I → Type*} [∀ r,Fintype (A r)] {R : Type*} [CommSemiring R]

/-- Arbitrary varying finite color alphabets factor under literal tensor interactions. -/
theorem partition_tensor (G : MultiGraph V E) (M : ∀ r,Matrix (A r) (A r) R) :
    G.partition (tensor M) (fun _=>1) = ∏ r,G.partition (M r) (fun _=>1) := by
  classical
  simp only [MultiGraph.partition,MultiGraph.assignmentWeight_one]
  let e : (V→∀r,A r) ≃ (∀r,V→A r) := Equiv.piComm (fun _ r=>A r)
  calc
    _ = ∑ σ : ∀r,V→A r, ∏r, ∏a, M r (σ r (G.src a)) (σ r (G.dst a)) := by
      apply Fintype.sum_equiv e
      intro σ
      exact Finset.prod_comm
    _ = _ := (Fintype.prod_sum (fun r (σ : V→A r)=>∏a,M r (σ (G.src a)) (σ (G.dst a)))).symm

/-- Number of retained size-s Potts factors. -/
def selectedMultiplicity {d : ℕ} (sizes : Fin d→ℕ) (s : ℕ) : ℕ :=
  (Finset.univ.filter (fun r=>sizes r=s)).card

/-- Number of unused colors in the all-ones tensor factor. -/
def discardedColors {d : ℕ} (sizes : Fin d→ℕ) (s : ℕ) : ℕ :=
  ∏r∈Finset.univ.filter (fun r=>sizes r≠s),sizes r

def coordinateTarget {d : ℕ} (sizes : Fin d→ℕ) (s : ℕ) (r : Fin d) :
    Matrix (Fin (sizes r)) (Fin (sizes r)) R :=
  fun i j=>if sizes r=s ∧ i=j then 2 else 1

theorem coordinate_partition (G : MultiGraph V E) {d : ℕ}
    (sizes : Fin d→ℕ) (s : ℕ) (r : Fin d) :
    G.partition (coordinateTarget (R:=R) sizes s r) (fun _=>1) =
      if sizes r=s then G.partition (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) R)
        (fun _=>1) else (sizes r:R)^Fintype.card V := by
  by_cases h : sizes r=s
  · have he : coordinateTarget (R:=R) sizes s r =
        (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin (sizes r)) (Fin (sizes r)) R) := by
      funext i j
      simp only [coordinateTarget,h,true_and,FullLogarithmicProductIdentities.pottsMatrix]
    rw [he,if_pos h]
    subst s
    rfl
  · have he : coordinateTarget (R:=R) sizes s r = (fun _ _=>1) := by
      funext i j
      simp [coordinateTarget,h]
    rw [he,if_neg h,MultiGraph.partition_allOnes]
    simp

theorem selectedMultiplicity_pos {d : ℕ} (sizes : Fin d→ℕ) (s : ℕ)
    (h : ∃r,sizes r=s) : 0<selectedMultiplicity sizes s := by
  rw [selectedMultiplicity,Finset.card_pos]
  obtain ⟨r,hr⟩:=h
  exact ⟨r,by simp [hr]⟩

theorem discardedColors_pos {d : ℕ} (sizes : Fin d→ℕ) (s : ℕ)
    (hsizes : ∀r,0<sizes r) : 0<discardedColors sizes s := by
  exact Finset.prod_pos (fun r _=>hsizes r)

/-- Exact partition identity used for fixed positive-root Potts recovery. -/
theorem target_partition (G : MultiGraph V E) {K : IntermediateField ℚ ℝ} {q d : ℕ}
    (sizes : Fin d→ℕ) (s : ℕ) (e : Fin q≃Color sizes) :
    G.partition (targetK (K:=K) sizes s e) (fun _=>1) =
      (discardedColors sizes s:K)^Fintype.card V *
        (G.partition (FullLogarithmicProductIdentities.pottsMatrix : Matrix (Fin s) (Fin s) K)
          (fun _=>1))^selectedMultiplicity sizes s := by
  have ht : targetK (K:=K) sizes s e =
      (fun i j=>tensor (coordinateTarget (R:=K) sizes s) (e i) (e j)) := rfl
  rw [ht]
  rw [G.partition_reindexColors (tensor (coordinateTarget (R:=K) sizes s))
    (fun _ : Color sizes=>1) e,partition_tensor]
  simp_rw [coordinate_partition]
  rw [Finset.prod_ite]
  have hc : (∏r∈Finset.univ.filter (fun r : Fin d=>¬sizes r=s),(sizes r:K)^Fintype.card V) =
      (discardedColors sizes s:K)^Fintype.card V := by
    rw [Finset.prod_pow]
    simp only [discardedColors,Nat.cast_prod]
  rw [hc]
  simp only [Finset.prod_const,selectedMultiplicity]
  rw [mul_comm]

end PlanarHom.HammingPottsTensorPartition
