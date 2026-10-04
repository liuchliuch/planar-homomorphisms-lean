import PlanarHom.RadialPottsHereditaryEuler
import PlanarHom.RadialPottsCoefficientBoundarySum
import PlanarHom.PottsRadialValueNormalization

/-! The literal radial coefficient supplies the diagonal Tutte/random-cluster
sample. Hereditary boundary Euler is derived from full Euler in this theorem. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RadialPotts.Assembly
open MultiGraph FinitePermutationCycles PottsCentered PottsTwoStageInterpolation
variable {V E : Type} [Fintype V] [Fintype E] {k : ℕ}

def subsetChoiceEquiv (E : Type) [Fintype E] : Finset E ≃ (E → Bool) where
  toFun A e := decide (e∈A)
  invFun choice := Finset.univ.filter (fun e => choice e=true)
  left_inv A := by ext e; simp
  right_inv choice := by funext e; simp

theorem boundaryStateSum_eq_subsets (rotation : Equiv.Perm (Medial.Dart E)) (δ : ℚ) (k : ℕ) :
    boundaryStateSum rotation δ k=∑ A : Finset E,δ^(count (subsetBoundary rotation A)*k) := by
  simp only [boundaryStateSum,permutation_componentCount]
  symm
  exact Fintype.sum_equiv (subsetChoiceEquiv E) _ _ (fun _ => rfl)

theorem normalize_boundaryStateSum (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex)
    (hfull : Fintype.card V+count (subsetBoundary rotation Finset.univ)=
      Fintype.card E+2*G.componentCount Finset.univ) (δ : ℚ) (k : ℕ) :
    (δ^k)^Fintype.card V*boundaryStateSum rotation δ k=G.randomCluster ((δ^k)^2) (δ^k) := by
  rw [boundaryStateSum_eq_subsets,randomCluster,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  have he := hereditary_boundary_euler G rotation hcycles hsurj hfull A
  simp only [← pow_mul,← pow_add]
  congr 1
  nlinarith [congrArg (fun n : ℕ => n*k) he]

theorem boundaryStateSum_eq_radialValue (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex)
    (hfull : Fintype.card V+count (subsetBoundary rotation Finset.univ)=
      Fintype.card E+2*G.componentCount Finset.univ) (δ : ℚ) (hδ : δ≠0) (k : ℕ) :
    boundaryStateSum rotation δ k=radialValue G δ k := by
  apply mul_left_cancel₀ (pow_ne_zero _ (pow_ne_zero _ hδ))
  exact (normalize_boundaryStateSum G rotation hcycles hsurj hfull δ k).trans (normalize_radialValue G δ k).symm

/-- Exact coefficient supplied to the existing two-stage recovery machine. -/
theorem marked_coefficient_eq_radialValue (G : MultiGraph V E) (rotation : Equiv.Perm (Medial.Dart E))
    (hcycles : ∀a b,rotation.SameCycle a b ↔ G.dartVertex a=G.dartVertex b)
    (hsurj : Function.Surjective G.dartVertex)
    (hfull : Fintype.card V+count (subsetBoundary rotation Finset.univ)=
      Fintype.card E+2*G.componentCount Finset.univ)
    (q N : ℕ) (hq : 1<q) (hk : 0<k) (hN : (Finset.univ\longEdges E k).card<N) :
    (markedPolynomial (graph rotation k) q (longEdges E k) N).coeff
      (N*(longEdges E k).card+2*k^2*Fintype.card E)=radialValue G ((q:ℚ)-1) k := by
  rw [marked_coefficient_eq_boundaryStateSum rotation q N (by omega) hk hN]
  have hδ : (q:ℚ)-1≠0 := by
    have hq' : (1:ℚ)<q := by exact_mod_cast hq
    linarith
  exact boundaryStateSum_eq_radialValue G rotation hcycles hsurj hfull _ hδ k
end PlanarHom.RadialPotts.Assembly
