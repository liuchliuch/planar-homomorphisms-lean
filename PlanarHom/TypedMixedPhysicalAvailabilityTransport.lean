import PlanarHom.RectangularMixedPhysicalForms
import PlanarHom.TypedBipartiteContext
import PlanarHom.TypedYFamilyTransport

/-! Literal coordinate transport of mixed gadget sums into the finite ambient
color chart. These equalities make no availability assumptions. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TwoTerminal

/-- Color reindexing commutes with the complete finite gadget sum. -/
theorem coloredSignature_reindexColors {J E C D R : Type}
    [Fintype J] [Fintype E] [Fintype C] [Fintype D] [CommSemiring R]
    (G : TwoTerminal J E) (c : C ≃ D) (W : E→Matrix C C R) (w : C→R) :
    coloredSignature G (fun e=>Matrix.reindex c c (W e)) (fun d=>w (c.symm d))=
      Matrix.reindex c c (coloredSignature G W w) := by
  funext a b
  unfold coloredSignature
  change (∑ η : J→D,(∏v,w (c.symm (η v))) *
    ∏e,W e (c.symm (extend a b η (G.src e))) (c.symm (extend a b η (G.dst e))))=
      ∑ η : J→C,(∏v,w (η v))*∏e,W e (extend (c.symm a) (c.symm b) η (G.src e))
        (extend (c.symm a) (c.symm b) η (G.dst e))
  apply Fintype.sum_equiv ((Equiv.refl J).arrowCongr c.symm)
  intro η
  have hext (v : Bool⊕J) : c.symm (extend a b η v)=
      extend (c.symm a) (c.symm b) (((Equiv.refl J).arrowCongr c.symm) η) v := by
    cases v with
    | inl z => cases z <;> rfl
    | inr z => rfl
  simp only [hext]
  rfl

end PlanarHom.TwoTerminal

namespace PlanarHom.TypedBipartiteContext
open TypedBipartiteSpectral RectangularMixedGadgets
variable {x y : ℕ} {R : Type} [Field R]

/-- The mixed three-edge path gives the exact zero-extended rectangular Gram. -/
theorem threePath_mixed_gram_fin (B : Matrix (Fin x) (Fin y) R)
    (K : Matrix (Fin y) (Fin y) R) :
    TwoTerminal.coloredSignature TwoTerminal.threeEdgePath
      (TwoTerminal.seriesMatrices (crossFin B) (onYFin K)) (fun _=>1)=
      zeroExtendFin (y:=y) (B*K*B.transpose) := by
  have h := TwoTerminal.coloredSignature_reindexColors TwoTerminal.threeEdgePath
    (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y))
    (TwoTerminal.seriesMatrices (cross B) (onY (X:=Fin x) K)) (fun _ : Fin x⊕Fin y=> (1:R))
  have he : (fun e=>Matrix.reindex finSumFinEquiv finSumFinEquiv
      (TwoTerminal.seriesMatrices (cross B) (onY (X:=Fin x) K) e))=
      TwoTerminal.seriesMatrices (crossFin B) (onYFin K) := by
    funext e
    unfold TwoTerminal.seriesMatrices
    split <;> rfl
  rw [he,threePath_mixed_gram] at h
  exact h

/-- The unrestricted double diamond is the exact zero-extended physical Gram. -/
theorem doubleDiamond_physical_gram_fin (B : Matrix (Fin x) (Fin y) R)
    (K : Matrix (Fin x) (Fin x) R) (hK : K.transpose=K) :
    TwoTerminal.coloredSignature doubleDiamond
      (edgeMatrices (zeroExtendFin (y:=y) K) (crossFin B)) (fun _=>1)=
      zeroExtendFin (y:=y) (entrySquare (K*B)*(entrySquare (K*B)).transpose) := by
  have h := TwoTerminal.coloredSignature_reindexColors doubleDiamond
    (finSumFinEquiv : Fin x⊕Fin y≃Fin (x+y))
    (edgeMatrices (onX (Y:=Fin y) K) (cross B)) (fun _ : Fin x⊕Fin y=> (1:R))
  have he : (fun e=>Matrix.reindex finSumFinEquiv finSumFinEquiv
      (edgeMatrices (onX (Y:=Fin y) K) (cross B) e))=
      edgeMatrices (zeroExtendFin (y:=y) K) (crossFin B) := by
    funext e
    unfold edgeMatrices
    split <;> rfl
  rw [he,doubleDiamond_physical_gram B K hK] at h
  exact h

end PlanarHom.TypedBipartiteContext
