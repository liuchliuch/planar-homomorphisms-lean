import PlanarHom.TypedBipartiteContext
import PlanarHom.TypedGadgetAppendColoredReduction
import PlanarHom.TypedGadgetAppendRestrictedSemantics

/-! Literal private-X gadget sums and their field maps. These semantic bridges
retain intrinsic domains, including gadgets with isolated terminals or no edges. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TypedBipartiteContext
local instance (priority := 10000) gadgetDecEq (α : Type*) : DecidableEq α := Classical.decEq α
open PrescribedDomains TypedGadgetAppend TypedBipartiteSpectral
variable {x y p e bt : ℕ}

def privateXEquiv : (Fin p→Fin x) ≃
    {η : Fin p→Fin (x+y) // Allowed (domains x y) (fun _=>0) η} where
  toFun η := ⟨fun j=>leftEmbedding (η j),by intro j; exact ⟨η j,rfl⟩⟩
  invFun η j := Classical.choose (η.property j)
  left_inv η := by
    funext j
    apply Fin.castAdd_injective x y
    exact Classical.choose_spec ((show Allowed (domains x y) (fun _=>0)
      (fun j=>leftEmbedding (η j)) from (fun j=>⟨η j,rfl⟩)) j)
  right_inv η := by
    apply Subtype.ext
    funext j
    exact Classical.choose_spec (η.property j)

variable {K : Type} [Field K]

def xBlock (M : Fin bt→Matrix (Fin (x+y)) (Fin (x+y)) K) (l : Fin bt) : Matrix (Fin x) (Fin x) K :=
  fun i j=>M l (leftEmbedding i) (leftEmbedding j)

theorem coloredDomainInteraction_X (G : TwoTerminal (Fin p) (Fin e))
    (label : Fin e→Fin bt) (M : Fin bt→Matrix (Fin (x+y)) (Fin (x+y)) K) (i j : Fin x) :
    coloredDomainInteraction G label (fun _=>0) M (domains x y) (leftEmbedding i) (leftEmbedding j)=
      TwoTerminal.coloredSignature G (fun k=>xBlock M (label k)) (fun _=>1) i j := by
  let f : (Fin p→Fin (x+y))→K := fun η=>∏ k,M (label k)
    (TwoTerminal.extend (leftEmbedding i) (leftEmbedding j) η (G.src k))
    (TwoTerminal.extend (leftEmbedding i) (leftEmbedding j) η (G.dst k))
  have hs := sum_restricted_eq_indicators (domains x y) (fun _:Fin p=>0) f
  have he := (privateXEquiv (x:=x) (y:=y) (p:=p)).sum_comp (fun η=>f η.val)
  have hc : (∑ η : Fin p→Fin (x+y),(∏ j,indicator (domains x y 0) (η j))*f η)=
      ∑ η : Fin p→Fin x, f (fun j=>leftEmbedding (η j)) := by
    calc
      _ = ∑ η : Fin p→Fin (x+y),f η*(∏ j,indicator (domains x y 0) (η j)) := by
        apply Finset.sum_congr rfl
        intro η _
        exact mul_comm _ _
      _ = ∑ η : {η : Fin p→Fin (x+y) // Allowed (domains x y) (fun _=>0) η},f η.val := hs.symm
      _ = _ := by
        rw [←he]
        rfl
  unfold coloredDomainInteraction TwoTerminal.coloredSignature
  simp only [Finset.prod_const_one,one_mul]
  refine Eq.trans ?_ (Eq.trans hc ?_)
  · apply Finset.sum_congr (by ext; simp)
    intro η _
    rfl
  · apply Finset.sum_congr (by ext; simp)
    intro η _
    have hext (v : Bool ⊕ Fin p) :
        TwoTerminal.extend (leftEmbedding i) (leftEmbedding j) (fun j=>leftEmbedding (η j)) v =
          leftEmbedding (y:=y) (TwoTerminal.extend i j η v) := by
      cases v with
      | inl b => cases b <;> rfl
      | inr v => rfl
    apply Finset.prod_congr rfl
    intro k _
    change M (label k)
      (TwoTerminal.extend (leftEmbedding i) (leftEmbedding j) (fun j=>leftEmbedding (η j)) (G.src k))
      (TwoTerminal.extend (leftEmbedding i) (leftEmbedding j) (fun j=>leftEmbedding (η j)) (G.dst k))=_
    rw [hext,hext]
    rfl

end PlanarHom.TypedBipartiteContext
