import PlanarHom.ColoringExposedPaletteNetwork
import PlanarHom.ColoringClausePrivateNumbering
import PlanarHom.FiniteBlockAllocation

/-! Explicit finite-index charts for the actual clause/palette/copy macros.
The forward maps follow contiguous numeric allocation and retain every edge
occurrence. No cardinality-only or noncomputable enumeration is used to emit IDs.
-/
noncomputable section
open Classical
namespace PlanarHom.ColoringMacroNumericCharts
open ColoringPaletteNetwork ColoringPalettePairCopy PlanarColoringClause

variable {n c l p : ℕ}

def coreParts : ColoringPaletteNetwork.Vertex (Fin n) (Fin c) (Fin l) ≃
    Fin n ⊕ ((Fin c × Fin 102) ⊕ Fin l) :=
  Equiv.sumCongr (Equiv.refl _) (
    (Equiv.sumAssoc (Fin c × (Fin 3 × Bool)) (Fin c × InternalVertex) (Fin l)).symm.trans
      (Equiv.sumCongr
        ((Equiv.prodSumDistrib (Fin c) (Fin 3 × Bool) InternalVertex).symm.trans
          (Equiv.prodCongr (Equiv.refl _) privateIndex)) (Equiv.refl _)))

def _root_.PlanarHom.ColoringPalettePairCopy.Shape.auxCount : Shape → ℕ | .single => 1 | .double => 4

def _root_.PlanarHom.ColoringPalettePairCopy.Shape.internalParts (s : Shape) : s.Internal ≃ (Fin 2 ⊕ Fin s.auxCount) :=
  match s with
  | .single => (@finSumFinEquiv 2 1).symm
  | .double => (@finSumFinEquiv 2 4).symm

def copyParts (shape : Fin p → Shape) : ((i : Fin p) × (shape i).Internal) ≃
    (Fin p × Fin 2) ⊕ ((i : Fin p) × Fin (shape i).auxCount) :=
  (Equiv.sigmaCongrRight (fun i => (shape i).internalParts)).trans
    ((Equiv.sigmaSumDistrib (fun _ : Fin p => Fin 2) (fun i => Fin (shape i).auxCount)).trans
      (Equiv.sumCongr (Equiv.sigmaEquivProd _ _) (Equiv.refl _)))

def copyIndex (shape : Fin p → Shape) : ((i : Fin p) × (shape i).Internal) ≃
    Fin (p*2+∑ i,(shape i).auxCount) :=
  (copyParts shape).trans ((Equiv.sumCongr finProdFinEquiv finSigmaFinEquiv).trans finSumFinEquiv)

def middleSwap (A B C D : Type) : ((A ⊕ (B ⊕ C)) ⊕ D) ≃ (A ⊕ (B ⊕ (D ⊕ C))) :=
  (Equiv.sumAssoc A (B ⊕ C) D).trans
    (Equiv.sumCongr (Equiv.refl A) ((Equiv.sumAssoc B C D).trans
      (Equiv.sumCongr (Equiv.refl B) (Equiv.sumComm C D))))

def vertexTotal (shape : Fin p → Shape) : ℕ := n+(c*102+((p*2+∑ i,(shape i).auxCount)+l))

def vertexIndex (shape : Fin p → Shape) :
    ColoringExposedPaletteNetwork.Vertex (V := Fin n) (C := Fin c) (L := Fin l) shape ≃
      Fin (vertexTotal (n := n) (c := c) (l := l) shape) :=
  (Equiv.sumCongr coreParts (Equiv.refl _)).trans
    ((middleSwap _ _ _ _).trans
      ((Equiv.sumCongr (Equiv.refl _)
        ((Equiv.sumCongr finProdFinEquiv
          ((Equiv.sumCongr (copyIndex shape) (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv)).trans
        finSumFinEquiv))

def twoWayEdgeIndex : PlanarColoringTwoWayConverter.Edge ≃ Fin 26 :=
  (Equiv.sumCongr (Equiv.refl _) finSumFinEquiv).trans finSumFinEquiv

def oneWayEdgeIndex : PlanarColoringOneWayConverter.Edge ≃ Fin 76 :=
  (Equiv.sumCongr finProdFinEquiv
    ((Equiv.prodCongr finTwoEquiv.symm twoWayEdgeIndex).trans finProdFinEquiv)).trans finSumFinEquiv

def clauseEdgeIndex : PlanarColoringClause.Edge ≃ Fin 254 :=
  (Equiv.sumCongr
    ((Equiv.prodCongr (Equiv.refl _) oneWayEdgeIndex).trans finProdFinEquiv)
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv)).trans finSumFinEquiv

def _root_.PlanarHom.ColoringPalettePairCopy.Shape.edgeCount : Shape → ℕ | .single => 6 | .double => 13

def unitIndex : Unit ≃ Fin 1 where
  toFun _ := 0
  invFun _ := ()
  left_inv x := by cases x; rfl
  right_inv x := by fin_cases x; rfl

def _root_.PlanarHom.ColoringPalettePairCopy.Shape.edgeIndex (s : Shape) : s.Edge ≃ Fin s.edgeCount :=
  match s with
  | .single => Equiv.refl _
  | .double => (Equiv.sumCongr unitIndex
      ((Equiv.prodCongr finTwoEquiv.symm (Equiv.refl _)).trans finProdFinEquiv)).trans finSumFinEquiv

def copyEdgeIndex (shape : Fin p → Shape) : ((i : Fin p) × (shape i).Edge) ≃
    Fin (∑ i,(shape i).edgeCount) :=
  (Equiv.sigmaCongrRight (fun i => (shape i).edgeIndex)).trans finSigmaFinEquiv

def edgeTotal (shape : Fin p → Shape) : ℕ := c*254+((∑ i,(shape i).edgeCount)+l*6)

def edgeIndex (shape : Fin p → Shape) :
    ColoringExposedPaletteNetwork.Edge (C := Fin c) (L := Fin l) shape ≃
      Fin (edgeTotal (c := c) (l := l) shape) :=
  (Equiv.sumAssoc _ _ _).trans
    ((Equiv.sumCongr (Equiv.refl _) (Equiv.sumComm _ _)).trans
      ((Equiv.sumCongr
        ((Equiv.prodCongr (Equiv.refl _) clauseEdgeIndex).trans finProdFinEquiv)
        ((Equiv.sumCongr (copyEdgeIndex shape) finProdFinEquiv).trans finSumFinEquiv)).trans finSumFinEquiv))

@[simp] theorem vertexIndex_primary (shape : Fin p → Shape) (v : Fin n) :
    (vertexIndex (n := n) (c := c) (l := l) shape (.inl (.inl v))).val=v.val := rfl

@[simp] theorem vertexIndex_palette (shape : Fin p → Shape) (i : Fin c) (k : Fin 3) (b : Bool) :
    (vertexIndex (n := n) (c := c) (l := l) shape (.inl (.inr (.inl (i,k,b))))).val=
      n+(compress (paletteVertex (k,b))+102*i.val) := rfl

@[simp] theorem vertexIndex_private (shape : Fin p → Shape) (i : Fin c) (v : InternalVertex) :
    (vertexIndex (n := n) (c := c) (l := l) shape (.inl (.inr (.inr (.inl (i,v)))))).val=
      n+(compress v.val+102*i.val) := rfl

@[simp] theorem vertexIndex_link (shape : Fin p → Shape) (i : Fin l) :
    (vertexIndex (n := n) (c := c) (l := l) shape (.inl (.inr (.inr (.inr i))))).val=
      n+(c*102+((p*2+∑ j,(shape j).auxCount)+i.val)) := rfl

@[simp] theorem edgeIndex_clause (shape : Fin p → Shape) (i : Fin c) (e : PlanarColoringClause.Edge) :
    (edgeIndex (c := c) (l := l) shape (.inl (.inl (i,e)))).val=(clauseEdgeIndex e).val+254*i.val := rfl

@[simp] theorem edgeIndex_link (shape : Fin p → Shape) (i : Fin l) (e : Fin 6) :
    (edgeIndex (c := c) (l := l) shape (.inl (.inr (i,e)))).val=
      c*254+((∑ j,(shape j).edgeCount)+(e.val+6*i.val)) := rfl

/-- Literal numeric clause replacement, with the original primary IDs shared
and all non-primary clause vertices in their 102-vertex private block. -/
def clauseVertexNumber (occurrence : Fin c → Fin 3 → Fin n) (i : Fin c)
    (v : PlanarColoringClause.Vertex) : ℕ :=
  if v.val=0 then (occurrence i 0).val else
    if v.val=34 then (occurrence i 1).val else
      if v.val=68 then (occurrence i 2).val else n+(compress v+102*i.val)

theorem vertexIndex_clauseMap (shape : Fin p → Shape) (occurrence : Fin c → Fin 3 → Fin n)
    (i : Fin c) (v : Fin 9 ⊕ InternalVertex) :
    (vertexIndex (n := n) (c := c) (l := l) shape
      (.inl (ColoringPaletteNetwork.clauseMap occurrence i v))).val=
        clauseVertexNumber occurrence i (labels v) := by
  cases v with
  | inl k => fin_cases k <;> rfl
  | inr v =>
    have h0 : v.val.val≠0 := fun h => v.property (primary_port v.val (Or.inl (Fin.ext h)))
    have h34 : v.val.val≠34 := fun h => v.property (primary_port v.val (Or.inr (Or.inl (Fin.ext h))))
    have h68 : v.val.val≠68 := fun h => v.property (primary_port v.val (Or.inr (Or.inr (Fin.ext h))))
    change _=clauseVertexNumber occurrence i v.val
    simp only [clauseVertexNumber,if_neg h0,if_neg h34,if_neg h68]
    rfl

theorem vertexIndex_clauseOriginal (shape : Fin p → Shape) (occurrence : Fin c → Fin 3 → Fin n)
    (i : Fin c) (v : PlanarColoringClause.Vertex) :
    (vertexIndex (n := n) (c := c) (l := l) shape
      (.inl (ColoringPaletteNetwork.clauseMap occurrence i (labels.symm v)))).val=
        clauseVertexNumber occurrence i v := by
  rw [vertexIndex_clauseMap,Equiv.apply_symm_apply]

end PlanarHom.ColoringMacroNumericCharts
