import PlanarHom.PottsRandomClusterPolynomial
import PlanarHom.MixedParallelSemantics
import PlanarHom.RootedHomogeneousSemantics

/-! Exact arbitrary-rational random-cluster parallel replacement for the actual
numeric occurrence code. Polynomial identity extends the proved finite-color
expansion, so no positive-integer restriction is imposed on the color variable. -/
noncomputable section
open Classical
namespace PlanarHom.Complexity.MixedCode
open MultiGraph
variable {C : Type} [Fintype C]

theorem unweighted_parallelCode (g : MixedCode) (hg : g.Valid 1 0) (l : ℕ)
    (M : Matrix C C ℚ) :
    ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)).unweighted M=
      (g.toMultiGraph hg).unweighted (fun i j => M i j^l) := by
  change ((g.parallelLabel 0 l).toMultiGraph _).partition M (fun _ => 1)=_
  rw [← evaluate_homogeneous (g.parallelLabel 0 l) (parallelLabel_valid 0 l 1 0 g hg)]
  rw [evaluate_parallelLabel g hg 0 l]
  have hm : (fun (j : Fin 1) i k => if j.val=0 then M i k^l else M i k)=
      fun (_ : Fin 1) i k => M i k^l := by
    funext j i k
    have : j.val=0 := by omega
    simp [this]
  rw [hm,evaluate_homogeneous]
  rfl

theorem randomCluster_parallelCode_nat (g : MixedCode) (hg : g.Valid 1 0)
    (l q : ℕ) (v : ℚ) :
    ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)).randomCluster q v=
      (g.toMultiGraph hg).randomCluster q ((1+v)^l-1) := by
  rw [← weighted_randomCluster,← weighted_randomCluster,unweighted_parallelCode g hg l]
  congr 1
  funext i j
  by_cases h : i=j <;> simp [h,add_comm]

theorem randomCluster_parallelCode (g : MixedCode) (hg : g.Valid 1 0)
    (l : ℕ) (Q v : ℚ) :
    ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)).randomCluster Q v=
      (g.toMultiGraph hg).randomCluster Q ((1+v)^l-1) := by
  let P := ((g.parallelLabel 0 l).toMultiGraph (parallelLabel_valid 0 l 1 0 g hg)).randomClusterColorPolynomial v
  let R := (g.toMultiGraph hg).randomClusterColorPolynomial ((1+v)^l-1)
  have hpoly : P=R := by
    apply Polynomial.eq_of_infinite_eval_eq
    apply (Set.infinite_range_of_injective (Nat.cast_injective (R:=ℚ))).mono
    intro x hx
    obtain ⟨n,rfl⟩ := hx
    simpa only [P,R,eval_randomClusterColorPolynomial] using randomCluster_parallelCode_nat g hg l n v
  simpa only [P,R,eval_randomClusterColorPolynomial] using congrArg (Polynomial.eval Q) hpoly
end PlanarHom.Complexity.MixedCode
