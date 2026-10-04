import PlanarHom.Gadgets
import PlanarHom.PlanarEmbedding

/-! NEW exact automorphism equivariance of finite edge-gadget signatures.
The separation predicate retains an actual planar cofacial-terminal gadget
for each color pair. Numerical separating matrices are not substituted. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TwoTerminal
variable {I E C R:Type} [Fintype I] [Fintype E] [Fintype C] [CommSemiring R]

 theorem extend_colorPermutation (p:Equiv.Perm C) (i j:C) (σ:I→C) (v:Bool⊕I) :
    extend (p i) (p j) (fun x=>p (σ x)) v=p (extend i j σ v) := by
  cases v with
  | inl b => cases b <;> rfl
  | inr v => rfl

 theorem assignmentWeight_colorPermutation (G:TwoTerminal I E) (M:Matrix C C R) (w:C→R)
    (p:Equiv.Perm C) (hM:∀i j,M (p i) (p j)=M i j) (hw:∀i,w (p i)=w i)
    (i j:C) (σ:I→C) :
    assignmentWeight G M w (p i) (p j) (fun x=>p (σ x))=assignmentWeight G M w i j σ := by
  simp only [assignmentWeight,edgeWeight,extend_colorPermutation,hM,hw]

 theorem signature_colorPermutation (G:TwoTerminal I E) (M:Matrix C C R) (w:C→R)
    (p:Equiv.Perm C) (hM:∀i j,M (p i) (p j)=M i j) (hw:∀i,w (p i)=w i) (i j:C) :
    signature G M w (p i) (p j)=signature G M w i j := by
  symm
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _:I=>p))
  intro σ
  exact (assignmentWeight_colorPermutation G M w p hM hw i j σ).symm

end PlanarHom.TwoTerminal
namespace PlanarHom.GadgetDiagonalSeparation
variable {C:Type} [Fintype C]

 def Separates (M:Matrix C C ℝ) : Prop :=
  ∀i j,i≠j→∃n m,∃G:TwoTerminal (Fin n) (Fin m),
    TwoTerminal.PlanarEdgeGadget G ∧
      G.signature M (fun _=>1) i i≠G.signature M (fun _=>1) j j

 theorem automorphism_fixed (M:Matrix C C ℝ) (hsep:Separates M)
    (p:Equiv.Perm C) (hp:∀i j,M (p i) (p j)=M i j) (i:C) : p i=i := by
  by_contra h
  obtain ⟨n,m,G,hG,hs⟩:=hsep (p i) i h
  exact hs (TwoTerminal.signature_colorPermutation G M (fun _=>1) p hp (fun _=>rfl) i i)

 theorem automorphism_eq_refl (M:Matrix C C ℝ) (hsep:Separates M)
    (p:Equiv.Perm C) (hp:∀i j,M (p i) (p j)=M i j) : p=Equiv.refl C :=
  Equiv.ext (automorphism_fixed M hsep p hp)

end PlanarHom.GadgetDiagonalSeparation
