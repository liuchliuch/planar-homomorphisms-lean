import PlanarHom.TypedMixedPhysicalAvailabilityOperation
import PlanarHom.RectangularMixedPhysicalForms
import PlanarHom.ColoredGadgetReindex

/-! Literal prescribed-domain sums for the two physical mixed gadgets. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TypedBipartiteContext
open TypedGadgetAppend PrescribedDomains TypedBipartiteSpectral
variable {q dt n p e : ℕ} {R : Type} [Field R]

/-- Intrinsic restrictions can be removed from a particular sum only after
proving that every nonzero product already obeys each original private tag. -/
theorem coloredDomainInteraction_eq_coloredSignature
    (D : Fin dt→Set (Fin q)) (A : Fin n→Matrix (Fin q) (Fin q) R)
    (G : TwoTerminal (Fin p) (Fin e)) (label : Fin e→Fin n) (tag : Fin p→Fin dt)
    (a b : Fin q)
    (hsupport : ∀η : Fin p→Fin q,
      (∏ k,A (label k) (TwoTerminal.extend a b η (G.src k))
        (TwoTerminal.extend a b η (G.dst k)))≠0 → Allowed D tag η) :
    coloredDomainInteraction G label tag A D a b =
      TwoTerminal.coloredSignature G (fun k=>A (label k)) (fun _=>1) a b := by
  unfold coloredDomainInteraction TwoTerminal.coloredSignature
  simp only [Finset.prod_const_one,one_mul]
  apply Finset.sum_congr (by ext; simp)
  intro η _
  rw [indicator_product]
  by_cases hz : (∏ k,A (label k) (TwoTerminal.extend a b η (G.src k))
      (TwoTerminal.extend a b η (G.dst k)))=0
  · simp only [hz,mul_zero]
  · rw [if_pos (hsupport η hz),one_mul]

/-- The path uses two private vertices, both carrying the original Y tag. -/
def mixedThreePath : TwoTerminal (Fin 2) (Fin 3) :=
  TwoTerminal.threeEdgePath.reindexInternal finTwoEquiv.symm (Equiv.refl _)

def mixedThreeLabel : Fin 3→Fin 2 := fun k=>if k.val=1 then 0 else 1

def mixedThreeTag : Fin 2→Fin 2 := fun _=>1

theorem mixedThreePath_planar : TwoTerminal.PlanarEdgeGadget mixedThreePath :=
  TwoTerminal.reindexInternal_planar _ _ _ TwoTerminal.threeEdgePath_planarEdgeGadget

theorem mixedThreePath_edges : ∀a b : Fin 2,sameX a b→∀k,
    (![sameY,crossPolicy] : Fin 2→Fin 2→Fin 2→Prop) (mixedThreeLabel k)
      (TwoTerminal.extend a b mixedThreeTag (mixedThreePath.src k))
      (TwoTerminal.extend a b mixedThreeTag (mixedThreePath.dst k)) := by
  intro a b hab k
  obtain ⟨rfl,rfl⟩ := hab
  fin_cases k <;> simp [mixedThreeLabel,mixedThreeTag,mixedThreePath,
    TwoTerminal.reindexInternal,MultiGraph.reindex,TwoTerminal.threeEdgePath,
    TwoTerminal.extend,sameY,crossPolicy]

/-- Exactly the side assignment certified for the literal eight occurrences. -/
def mixedDiamondTag : Fin 5→Fin 2 := fun k=>RectangularMixedGadgets.vertexSide (.inr k)

theorem mixedDiamond_edges : ∀a b : Fin 2,sameX a b→∀k,
    (![sameX,crossPolicy] : Fin 2→Fin 2→Fin 2→Prop) (RectangularMixedGadgets.label k)
      (TwoTerminal.extend a b mixedDiamondTag (RectangularMixedGadgets.doubleDiamond.src k))
      (TwoTerminal.extend a b mixedDiamondTag (RectangularMixedGadgets.doubleDiamond.dst k)) := by
  intro a b hab k
  obtain ⟨rfl,rfl⟩ := hab
  fin_cases k <;> simp [mixedDiamondTag,RectangularMixedGadgets.vertexSide,
    RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
    TwoTerminal.extend,sameX,crossPolicy]

variable {x y : ℕ}

theorem mixedThree_interaction_eq_signature
    (K B : Matrix (Fin (x+y)) (Fin (x+y)) R)
    (hK : ∀i j,K i j≠0 → i∈domains x y 1 ∧ j∈domains x y 1) :
    coloredDomainInteraction mixedThreePath mixedThreeLabel mixedThreeTag ![K,B] (domains x y)=
      TwoTerminal.coloredSignature mixedThreePath
        (fun k=>(![K,B] : Fin 2→Matrix _ _ R) (mixedThreeLabel k)) (fun _=>1) := by
  funext a b
  apply coloredDomainInteraction_eq_coloredSignature
  intro η hη
  have he := (Finset.prod_ne_zero_iff.mp hη) (1:Fin 3) (Finset.mem_univ _)
  have hn : K (η 0) (η 1)≠0 := by
    simpa [mixedThreeLabel,mixedThreePath,TwoTerminal.reindexInternal,
      MultiGraph.reindex,TwoTerminal.threeEdgePath,TwoTerminal.extend] using he
  intro j
  fin_cases j
  · exact (hK _ _ hn).1
  · exact (hK _ _ hn).2

theorem mixedDiamond_interaction_eq_signature
    (K B : Matrix (Fin (x+y)) (Fin (x+y)) R)
    (hK : ∀i j,K i j≠0 → i∈domains x y 0 ∧ j∈domains x y 0)
    (hB : ∀i j,i∈domains x y 0 → B i j≠0 → j∈domains x y 1) :
    coloredDomainInteraction RectangularMixedGadgets.doubleDiamond RectangularMixedGadgets.label
      mixedDiamondTag ![K,B] (domains x y)=
      TwoTerminal.coloredSignature RectangularMixedGadgets.doubleDiamond
        (RectangularMixedGadgets.edgeMatrices K B) (fun _=>1) := by
  have heq : (fun k=>(![K,B] : Fin 2→Matrix _ _ R) (RectangularMixedGadgets.label k))=
      RectangularMixedGadgets.edgeMatrices K B := by
    funext k
    fin_cases k <;> simp [RectangularMixedGadgets.label,RectangularMixedGadgets.edgeMatrices]
  rw [←heq]
  funext a b
  apply coloredDomainInteraction_eq_coloredSignature
  intro η hη
  have he k := (Finset.prod_ne_zero_iff.mp hη) k (Finset.mem_univ _)
  have h0 : K a (η 0)≠0 := by
    simpa [RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
      TwoTerminal.extend] using he 0
  have h2 : K a (η 1)≠0 := by
    simpa [RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
      TwoTerminal.extend] using he 2
  have h5 : K (η 3) b≠0 := by
    simpa [RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
      TwoTerminal.extend] using he 5
  have h7 : K (η 4) b≠0 := by
    simpa [RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
      TwoTerminal.extend] using he 7
  have h1 : B (η 0) (η 2)≠0 := by
    simpa [RectangularMixedGadgets.label,RectangularMixedGadgets.doubleDiamond,
      TwoTerminal.extend] using he 1
  intro j
  fin_cases j <;> simp only [mixedDiamondTag,RectangularMixedGadgets.vertexSide]
  · exact (hK _ _ h0).2
  · exact (hK _ _ h2).2
  · exact hB _ _ (hK _ _ h0).2 h1
  · exact (hK _ _ h5).1
  · exact (hK _ _ h7).1

end PlanarHom.TypedBipartiteContext
