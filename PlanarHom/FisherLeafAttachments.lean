import PlanarHom.FisherRootedFamily
import PlanarHom.RootedLoop

/-! Ordinary planarity of finite oriented leaf and loop attachments. -/
noncomputable section
open Classical

namespace PlanarHom.Fisher
open MultiGraph

def rootedEdge (forward : Bool) : RootedGraph Unit Unit where
  src _ := if forward then Sum.inl PUnit.unit else Sum.inr ()
  dst _ := if forward then Sum.inr () else Sum.inl PUnit.unit

open unitInterval in
def rootedEdgeDrawing (b : Bool) : PlaneDrawing (rootedEdge b) where
  point := Sum.elim (fun _ => (0,0)) (fun _ => (1,0))
  point_injective := by
    rintro (u | u) (v | v) h <;> simp_all
  curve _ :=
    { toFun := fun t => (if b then ((t : ℝ), 0) else (1 - (t : ℝ), 0))
      continuous_toFun := by cases b <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop }
  curve_zero _ := by cases b <;> simp [rootedEdge]
  curve_one _ := by cases b <;> simp [rootedEdge]
  interior_injective e f s t hs ht h := by
    refine ⟨Subsingleton.elim e f, ?_⟩
    apply Subtype.ext
    have hh := congrArg Prod.fst h
    cases b <;> simp_all
  interior_avoids e t ht v h := by
    have hh := congrArg Prod.fst h
    cases b
    · cases v
      · change 1 - (t : ℝ) = 0 at hh
        linarith [ht.2]
      · change 1 - (t : ℝ) = 1 at hh
        linarith [ht.1]
    · cases v
      · change (t : ℝ) = 0 at hh
        linarith [ht.1]
      · change (t : ℝ) = 1 at hh
        linarith [ht.2]

def sigmaUniqueEquiv {I : Type*} (W : I → Type*) [∀ i, Unique (W i)] : Sigma W ≃ I where
  toFun := Sigma.fst
  invFun i := ⟨i, default⟩
  left_inv := by
    rintro ⟨i,w⟩
    exact congrArg (Sigma.mk i) (Subsingleton.elim _ _)
  right_inv _ := rfl

end PlanarHom.Fisher

namespace PlanarHom.MultiGraph
open Fisher
variable {V E I : Type*}

def addLeaves (G : MultiGraph V E) (root : I → V) (forward : I → Bool) :
    MultiGraph (V ⊕ I) (E ⊕ I) where
  src := Sum.elim (fun e => Sum.inl (G.src e))
    (fun i => if forward i then Sum.inl (root i) else Sum.inr i)
  dst := Sum.elim (fun e => Sum.inl (G.dst e))
    (fun i => if forward i then Sum.inr i else Sum.inl (root i))

def addLeavesAttachmentEquiv (G : MultiGraph V E) (root : I → V) (forward : I → Bool) :
    IncidenceEquiv (G.attachFamily root (fun i => rootedEdge (forward i)))
      (G.addLeaves root forward) where
  vertex := Equiv.sumCongr (Equiv.refl _) (sigmaUniqueEquiv (fun _ : I => Unit))
  edge := Equiv.sumCongr (Equiv.refl _) (sigmaUniqueEquiv (fun _ : I => Unit))
  src_eq := by
    rintro (e | ⟨i,⟨⟩⟩)
    · rfl
    · cases h : forward i <;>
        simp [addLeaves, attachFamily, attachFamilyVertex, rootedEdge, sigmaUniqueEquiv, h]
  dst_eq := by
    rintro (e | ⟨i,⟨⟩⟩)
    · rfl
    · cases h : forward i <;>
        simp [addLeaves, attachFamily, attachFamilyVertex, rootedEdge, sigmaUniqueEquiv, h]

theorem Planar.addLeaves [Finite V] [Finite E] [Fintype I] {G : MultiGraph V E}
    (hG : G.Planar) (root : I → V) (forward : I → Bool) :
    (G.addLeaves root forward).Planar :=
  (addLeavesAttachmentEquiv G root forward).planar_iff.mp
    (hG.attachFamily root (fun i => rootedEdge (forward i)) (fun _ => ⟨rootedEdgeDrawing _⟩))

def addIndexedLoops (G : MultiGraph V E) (root : I → V) : MultiGraph V (E ⊕ I) where
  src := Sum.elim G.src root
  dst := Sum.elim G.dst root

def addLoopsAttachmentEquiv (G : MultiGraph V E) (root : I → V) :
    IncidenceEquiv (G.attachFamily root (fun _ => RootedGraph.singleLoop))
      (G.addIndexedLoops root) where
  vertex := by
    letI : IsEmpty (Σ _ : I, Fin 0) := ⟨fun q => q.2.elim0⟩
    exact sumEmptyEquiv V (Σ _ : I, Fin 0)
  edge := Equiv.sumCongr (Equiv.refl _) (sigmaUniqueEquiv (fun _ : I => Fin 1))
  src_eq := by
    rintro (e | ⟨i,e⟩)
    · rfl
    · rfl
  dst_eq := by
    rintro (e | ⟨i,e⟩)
    · rfl
    · rfl

theorem Planar.addIndexedLoops [Finite V] [Finite E] [Fintype I] {G : MultiGraph V E}
    (hG : G.Planar) (root : I → V) : (G.addIndexedLoops root).Planar :=
  (addLoopsAttachmentEquiv G root).planar_iff.mp
    (hG.attachFamily root (fun _ => RootedGraph.singleLoop) (fun _ => RootedGraph.singleLoop_planar))

end PlanarHom.MultiGraph
