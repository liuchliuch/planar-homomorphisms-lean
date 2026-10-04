import PlanarHom.ColoringFramedCanvasRetention
import PlanarHom.RotationRowsMarkerErasure

/-! An explicit retained/deleted dart partition for the literal framed graph.
Only auxiliary marker enumeration is noncomputable, and it is used solely in
the Euler proof. The actual numeric query rotation remains the computed one. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn ParsimoniousNorOneInThree

abbrev DeletedDart (f : NumericFormula) := {d : Dart f // keepDart f d=none}

def splitDarts (f : NumericFormula) : Dart f≃(MultiGraph.Kasteleyn.Dart (Canvas.Edge f)⊕DeletedDart f) where
  toFun d := if h:∃a,keepDart f d=some a then .inl h.choose else .inr ⟨d,by
    cases he:keepDart f d with
    | none => rfl
    | some a => exact False.elim (h ⟨a,he⟩)⟩
  invFun
    | .inl a => oldDart f a
    | .inr d => d.val
  left_inv d := by
    dsimp only
    split_ifs with h
    · exact (keepDart_eq_some_iff f d h.choose).mp h.choose_spec
    · rfl
  right_inv d := by
    dsimp only
    cases d with
    | inl a =>
      have h : ∃b,keepDart f (oldDart f a)=some b := ⟨a,keepDart_oldDart f a⟩
      simp only [dif_pos h]
      have ha : h.choose=a := Option.some.inj (h.choose_spec.symm.trans (keepDart_oldDart f a))
      rw [ha]
    | inr d =>
      have h : ¬∃a,keepDart f d.val=some a := by rw [d.property]; simp
      simp only [dif_neg h]

def markerCount (f : NumericFormula) : ℕ := Fintype.card (DeletedDart f)

def dartPartition (f : NumericFormula) : Dart f≃(MultiGraph.Kasteleyn.Dart (Canvas.Edge f)⊕Fin (markerCount f)) :=
  (splitDarts f).trans (Equiv.sumCongr (Equiv.refl _) (Fintype.equivFin (DeletedDart f)))

theorem partition_oldDart (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    dartPartition f (oldDart f a)=.inl a := by
  have h : ∃b,keepDart f (oldDart f a)=some b := ⟨a,keepDart_oldDart f a⟩
  have ha : h.choose=a := Option.some.inj (h.choose_spec.symm.trans (keepDart_oldDart f a))
  simp only [dartPartition,Equiv.trans_apply,splitDarts,Equiv.coe_fn_mk,dif_pos h,ha]
  rfl

theorem partition_symm_inl (f : NumericFormula) (a : MultiGraph.Kasteleyn.Dart (Canvas.Edge f)) :
    (dartPartition f).symm (.inl a)=oldDart f a := by
  apply (dartPartition f).injective
  rw [Equiv.apply_symm_apply,partition_oldDart]

theorem partition_keep (f : NumericFormula) (d : Dart f) :
    HostRowSystem.keepLeft (dartPartition f d)=keepDart f d := by
  by_cases h : ∃a,keepDart f d=some a
  · have hd : oldDart f h.choose=d := (keepDart_eq_some_iff f d h.choose).mp h.choose_spec
    rw [←hd,partition_oldDart,keepDart_oldDart]
    rfl
  · have hn : keepDart f d=none := by
      cases he:keepDart f d with
      | none => rfl
      | some a => exact False.elim (h ⟨a,he⟩)
    simp [dartPartition,splitDarts,h,hn,HostRowSystem.keepLeft]

end PlanarHom.ColoringEmitter.FramedCanvas
