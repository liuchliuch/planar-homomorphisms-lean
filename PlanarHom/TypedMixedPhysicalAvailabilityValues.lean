import PlanarHom.TypedMixedPhysicalAvailabilitySemantics
import PlanarHom.TypedMixedPhysicalAvailabilityTransport

/-! The prescribed private-domain sums have exactly the physical mixed values.
Every indicator is discharged by proved support of a literal gadget edge. -/
noncomputable section
open Classical
namespace PlanarHom.TypedBipartiteContext
open TypedGadgetAppend PrescribedDomains TypedBipartiteSpectral RectangularMixedGadgets
variable {x y : ℕ} {R : Type} [Field R]

theorem onYFin_nonzero_domains (K : Matrix (Fin y) (Fin y) R)
    (a b : Fin (x+y)) (h : onYFin K a b≠0) :
    a∈domains x y 1 ∧ b∈domains x y 1 := by
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b,rfl⟩ := finSumFinEquiv.surjective b
  rcases a with a|a <;> rcases b with b|b
  all_goals simp only [onYFin,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,onY,Matrix.fromBlocks] at h
  all_goals try contradiction
  exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩

theorem zeroExtendFin_nonzero_domains (K : Matrix (Fin x) (Fin x) R)
    (a b : Fin (x+y)) (h : zeroExtendFin K a b≠0) :
    a∈domains x y 0 ∧ b∈domains x y 0 := by
  obtain ⟨a,rfl⟩ := finSumFinEquiv.surjective a
  obtain ⟨b,rfl⟩ := finSumFinEquiv.surjective b
  rcases a with a|a <;> rcases b with b|b
  all_goals simp only [zeroExtendFin,Matrix.reindex_apply,Matrix.submatrix_apply,
    Equiv.symm_apply_apply,zeroExtend,Matrix.fromBlocks] at h
  all_goals try contradiction
  exact ⟨⟨a,rfl⟩,⟨b,rfl⟩⟩

theorem crossFin_nonzero_right_domain (B : Matrix (Fin x) (Fin y) R)
    (a b : Fin (x+y)) (ha : a∈domains x y 0) (h : crossFin B a b≠0) :
    b∈domains x y 1 := by
  obtain ⟨a,rfl⟩ := ha
  obtain ⟨b,rfl⟩ := finSumFinEquiv.surjective b
  rcases b with b|b
  · change cross B (finSumFinEquiv.symm (finSumFinEquiv (.inl a)))
      (finSumFinEquiv.symm (finSumFinEquiv (.inl b)))≠0 at h
    simp [cross] at h
  · exact ⟨b,rfl⟩

/-- The two Y-private vertices remain the original Y domain, even when the
retained language has arbitrary cross, XX, YY, or unary companions. -/
theorem mixedThree_physical_value (B : Matrix (Fin x) (Fin y) R)
    (K : Matrix (Fin y) (Fin y) R) :
    coloredDomainInteraction mixedThreePath mixedThreeLabel mixedThreeTag
      ![onYFin K,crossFin B] (domains x y)=zeroExtendFin (y:=y) (B*K*B.transpose) := by
  rw [mixedThree_interaction_eq_signature _ _ (onYFin_nonzero_domains K)]
  have he : (fun k=>(![onYFin K,crossFin B] : Fin 2→Matrix _ _ R) (mixedThreeLabel k))=
      TwoTerminal.seriesMatrices (crossFin B) (onYFin K) := by
    funext k
    fin_cases k <;> rfl
  rw [he]
  have hr := TwoTerminal.coloredSignature_reindexInternal TwoTerminal.threeEdgePath
    finTwoEquiv.symm (Equiv.refl (Fin 3))
    (TwoTerminal.seriesMatrices (crossFin B) (onYFin K)) (fun _=>1)
  change TwoTerminal.coloredSignature
    (TwoTerminal.threeEdgePath.reindexInternal finTwoEquiv.symm (Equiv.refl (Fin 3)))
    (TwoTerminal.seriesMatrices (crossFin B) (onYFin K)) (fun _=>1)=_
  simpa only [Equiv.refl_symm,Equiv.refl_apply] using
    hr.trans (threePath_mixed_gram_fin B K)

/-- The five private domains are X,X,Y,X,X, matching the actual eight-edge
mixed double diamond; this is not a B-only bipartite template. -/
theorem mixedDiamond_physical_value (B : Matrix (Fin x) (Fin y) R)
    (K : Matrix (Fin x) (Fin x) R) (hK : K.transpose=K) :
    coloredDomainInteraction doubleDiamond label mixedDiamondTag
      ![zeroExtendFin (y:=y) K,crossFin B] (domains x y)=
      zeroExtendFin (y:=y) (entrySquare (K*B)*(entrySquare (K*B)).transpose) := by
  rw [mixedDiamond_interaction_eq_signature _ _ (zeroExtendFin_nonzero_domains K)
    (crossFin_nonzero_right_domain B),doubleDiamond_physical_gram_fin B K hK]

end PlanarHom.TypedBipartiteContext
