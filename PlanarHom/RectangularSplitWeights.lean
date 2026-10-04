import PlanarHom.RectangularSourceOrthogonalData
import PlanarHom.RectangularSubsetCoefficients

/-! NEW exact multiplicative weights and finite boundary count for disjoint
Fourier decompositions. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RectangularWalshConvolution
open Boolean
variable {d:ℕ}

theorem characterWeight_product (θ:Fin d→ℝ) (S:Cube d):
    characterWeight θ S=∏i:Fin d,if S i then θ i else 1:=by
  simp only [characterWeight,bitSupport,Finset.prod_filter]

@[simp] theorem characterWeight_empty (θ:Fin d→ℝ):characterWeight θ (fun _=>false)=1:=by
  simp [characterWeight,bitSupport]

theorem characterWeight_split (θ:Fin d→ℝ) (S I:Cube d) (h:bitSupport I⊆bitSupport S):
    characterWeight θ I*characterWeight θ (xor S I)=characterWeight θ S:=by
  simp only [characterWeight_product,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have hi:(I i=true)→S i=true:=fun hi=>(mem_bitSupport S i).mp (h ((mem_bitSupport I i).mpr hi))
  by_cases hI:I i=true
  · have hS:=hi hI
    simp [Boolean.xor,hI,hS]
  · have hI':I i=false:=Bool.eq_false_iff.mpr hI
    simp [Boolean.xor,hI']

theorem proper_split_degrees (S:Cube d) (A:Finset (Fin d)) (hA:A⊆bitSupport S)
    (hne:A≠∅) (hproper:A≠bitSupport S):
    Boolean.degree (bitsOfSet A)<Boolean.degree S ∧
      Boolean.degree (xor S (bitsOfSet A))<Boolean.degree S:=by
  have hI:Boolean.degree (bitsOfSet A)=A.card:=by rw [degree_eq_support_card,support_bitsOfSet]
  have hsum:Boolean.degree (bitsOfSet A)+Boolean.degree (xor S (bitsOfSet A))=Boolean.degree S:=
    (minimal_split_iff S _).mpr (by simpa only [support_bitsOfSet] using hA)
  have hlt:A.card<(bitSupport S).card:=Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨hA,hproper⟩)
  have hpos:0<A.card:=Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hne)
  rw [←degree_eq_support_card] at hlt
  omega

theorem sum_powerset_boundary (s:Finset (Fin d)) (hs:s.Nonempty) (α β:ℝ):
    (∑A∈s.powerset,if A=∅ then α else if A=s then α else β)=
      2*α+((2:ℝ)^s.card-2)*β:=by
  have he (A:Finset (Fin d)):
      (if A=∅ then α else if A=s then α else β)=
      β+(if A=∅ then α-β else 0)+(if A=s then α-β else 0):=by
    by_cases h0:A=∅
    · subst A
      simp [hs.ne_empty,hs.ne_empty.symm] <;> ring
    · by_cases hA:A=s <;> simp [h0,hA,hs.ne_empty] <;> ring
  simp_rw [he]
  simp only [Finset.sum_add_distrib,Finset.sum_const,nsmul_eq_mul,Finset.card_powerset,
    Nat.cast_pow,Nat.cast_ofNat,Finset.sum_ite_eq',Finset.empty_mem_powerset,
    Finset.mem_powerset,Finset.Subset.refl,Finset.empty_subset,ite_true]
  ring

end PlanarHom.RectangularWalshConvolution
