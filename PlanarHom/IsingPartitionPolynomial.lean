import PlanarHom.Basic
import PlanarHom.BooleanTensorEasyAssembly
import PlanarHom.AlgebraPolynomialInterpolation
import Mathlib.Algebra.Polynomial.BigOperators

/-! NEW literal univariate Ising partition polynomial. Each occurrence is
counted separately in the disagreement exponent; loops contribute zero and
all assignments to isolated vertices remain in the finite sum. -/
noncomputable section
open Classical
open scoped BigOperators Polynomial
namespace PlanarHom.MultiGraph
variable {V E:Type*} [Fintype V] [Fintype E] (G:MultiGraph V E)

def isingDisagreements (σ:V→Bool) : ℕ :=
  (Finset.univ.filter (fun e:E=>σ (G.src e)≠σ (G.dst e))).card

def isingPartitionPolynomial : Polynomial ℚ :=
  ∑σ:V→Bool,Polynomial.X^(G.isingDisagreements σ)

theorem isingDisagreements_le (σ:V→Bool) : G.isingDisagreements σ≤Fintype.card E :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_univ)

theorem isingPartitionPolynomial_natDegree :
    G.isingPartitionPolynomial.natDegree≤Fintype.card E := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro σ _
  rw [Polynomial.natDegree_X_pow]
  exact G.isingDisagreements_le σ

theorem isingPartitionPolynomial_eval₂ {K:Type} [CommSemiring K] (f:ℚ→+*K) (ρ:K) :
    G.isingPartitionPolynomial.eval₂ f ρ=
      G.partition (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) := by
  simp only [isingPartitionPolynomial,Polynomial.eval₂_finset_sum,Polynomial.eval₂_pow,
    Polynomial.eval₂_X,partition,assignmentWeight_one]
  apply Finset.sum_congr rfl
  intro σ _
  simp [BooleanTensorEasyAssembly.isingMatrix,Finset.prod_ite,isingDisagreements]

theorem isingPartitionPolynomial_eval (ρ:ℚ) :
    G.isingPartitionPolynomial.eval ρ=
      G.partition (BooleanTensorEasyAssembly.isingMatrix ρ) (fun _=>1) :=
  G.isingPartitionPolynomial_eval₂ (RingHom.id ℚ) ρ

theorem isingPartitionPolynomial_edgeless [IsEmpty E] :
    G.isingPartitionPolynomial=Polynomial.C ((2:ℚ)^Fintype.card V) := by
  simp [isingPartitionPolynomial,isingDisagreements]
  exact congrArg (fun p:Polynomial ℚ=>p^Fintype.card V) (by exact (map_ofNat Polynomial.C 2).symm)

theorem isingPartitionPolynomial_empty [IsEmpty V] : G.isingPartitionPolynomial=1 := by
  letI:IsEmpty E:=Function.isEmpty G.src
  simp [G.isingPartitionPolynomial_edgeless]

end PlanarHom.MultiGraph
