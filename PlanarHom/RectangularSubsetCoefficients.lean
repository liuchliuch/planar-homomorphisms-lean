import PlanarHom.RectangularSingletonCoefficient
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

/-! NEW exact minimum-degree coefficient as a sum over the genuine subsets
of the source Fourier index. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean Polynomial
variable {d:ℕ}

def splitConvolution (C:Matrix (Cube d) (Cube d) ℝ) (S T I:Cube d):ℝ:=
  ∑J:Cube d,C I J*C (xor S I) (xor T J)

theorem squareCoefficient_subsets (C:Matrix (Cube d) (Cube d) ℝ) (S T:Cube d):
    (squareCoefficientPolynomial C S T).coeff (Boolean.degree S)=
      ∑A∈(bitSupport S).powerset,splitConvolution C S T (bitsOfSet A):=by
  rw [squarePolynomial_coeff]
  simp only [Fintype.sum_prod_type,minimal_split_iff]
  have hsum:∀I:Cube d,
      (∑J:Cube d,if bitSupport I⊆bitSupport S then C I J*C (xor S I) (xor T J) else 0)=
      if bitSupport I⊆bitSupport S then splitConvolution C S T I else 0:=by
    intro I
    by_cases h:bitSupport I⊆bitSupport S <;> simp [h,splitConvolution]
  simp_rw [hsum]
  trans ∑A:Finset (Fin d),if A⊆bitSupport S then splitConvolution C S T (bitsOfSet A) else 0
  · apply Fintype.sum_equiv (bitSetEquiv d)
    intro I
    change (if bitSupport I⊆bitSupport S then splitConvolution C S T I else 0)=
      if bitSupport I⊆bitSupport S then splitConvolution C S T (bitsOfSet (bitSupport I)) else 0
    rw [bitsOfSet_support]
  · rw [←Finset.sum_filter]
    congr 1
    ext A
    simp

@[simp] theorem bitsOfSet_empty:bitsOfSet (∅:Finset (Fin d))=(fun _=>false):=by
  funext i
  simp [bitsOfSet]
@[simp] theorem bitsOfSet_singleton (i:Fin d):bitsOfSet {i}=unitBit i:=by
  funext j
  simp [bitsOfSet,unitBit]

def pairBits (i k:Fin d):Cube d:=bitsOfSet {i,k}

@[simp] theorem support_pairBits (i k:Fin d):bitSupport (pairBits i k)={i,k}:=support_bitsOfSet _

theorem pairBits_degree (i k:Fin d) (hik:i≠k):Boolean.degree (pairBits i k)=2:=by
  rw [degree_eq_support_card,support_pairBits,Finset.card_pair hik]

theorem pairBits_xor_left (i k:Fin d) (hik:i≠k):xor (pairBits i k) (unitBit i)=unitBit k:=by
  funext j
  by_cases hji:j=i
  · subst j
    simp [Boolean.xor,pairBits,bitsOfSet,unitBit,hik]
  · by_cases hjk:j=k <;> simp [Boolean.xor,pairBits,bitsOfSet,unitBit,hji,hjk,hik,hik.symm]

theorem pairBits_xor_right (i k:Fin d) (hik:i≠k):xor (pairBits i k) (unitBit k)=unitBit i:=by
  have he:pairBits i k=pairBits k i:=by simp [pairBits,Finset.pair_comm]
  rw [he]
  exact pairBits_xor_left k i hik.symm

theorem squareCoefficient_pair_decomposition (C:Matrix (Cube d) (Cube d) ℝ)
    (i k:Fin d) (hik:i≠k) (T:Cube d):
    (squareCoefficientPolynomial C (pairBits i k) T).coeff 2=
      splitConvolution C (pairBits i k) T (fun _=>false)+
      splitConvolution C (pairBits i k) T (unitBit k)+
      splitConvolution C (pairBits i k) T (unitBit i)+
      splitConvolution C (pairBits i k) T (pairBits i k):=by
  rw [←pairBits_degree i k hik,squareCoefficient_subsets,support_pairBits]
  rw [Finset.sum_powerset_insert (by simpa using hik : i∉({k}:Finset (Fin d)))]
  have hp:({k}:Finset (Fin d)).powerset={∅,{k}}:=by
    ext s
    simp only [Finset.mem_powerset,Finset.mem_insert,Finset.mem_singleton]
    exact Finset.subset_singleton_iff
  rw [hp]
  rw [Finset.sum_pair ((Finset.singleton_ne_empty k).symm),
    Finset.sum_pair ((Finset.singleton_ne_empty k).symm)]
  simp only [bitsOfSet_empty,Finset.insert_empty,bitsOfSet_singleton]
  change _ = _
  simp only [pairBits]
  ring

end PlanarHom.RectangularWalshConvolution
