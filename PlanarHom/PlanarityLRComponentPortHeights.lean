import PlanarHom.PlanarityLRAllPortNoncrossing
import PlanarHom.OrderedPortTransport
import PlanarHom.RadialPottsAssemblyCircleArches

/-! NEW exact rank heights on the actual contour port word, with full paired
occurrence noninterleaving transported from the computed contour keys. -/
noncomputable section
namespace PlanarHom.PlanarityLRRealization
open Complexity MultiGraph.Kasteleyn PlanarityLRDirect PlanarityLRRawConstraints PlanarityLRConstraints
open PlanarityLRConstraintBlocks

 def componentPortWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base : Dart (Fin g.edges.length)) : List (Dart (Fin g.edges.length)) :=
  contourPortWord (directRotationRows g hg bits) (fun e => isTree g e.val) (componentContourStart g hg bits base)

 theorem mem_componentPortWord (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base a : Dart (Fin g.edges.length)) : a ∈ componentPortWord g hg bits base ↔
      componentRoot g (dartHost g base)=componentRoot g (dartHost g a) ∧ isTree g a.1.val=false := by
  rw [componentPortWord,mem_dfsContourPortWord,componentStart_componentRoot]

 theorem componentPortWord_key_sorted (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base : Dart (Fin g.edges.length)) : (componentPortWord g hg bits base).Pairwise
      (fun a b => contourKey g bits (eraseDart a) < contourKey g bits (eraseDart b)) := by
  have h := dfsContourWord_key_sorted g hg bits (componentContourStart g hg bits base)
    (componentStart_isRootFirst g hg bits base)
  exact h.filter (fun a => !(isTree g a.1.val))

 theorem componentPortWord_reverse_mem (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base : Dart (Fin g.edges.length)) {a : Dart (Fin g.edges.length)} (ha : a ∈ componentPortWord g hg bits base) :
    reversePerm _ a ∈ componentPortWord g hg bits base := by
  rw [mem_componentPortWord] at ha ⊢
  refine ⟨?_,ha.2⟩
  have h := reverse_componentRoot g hg (a := eraseDart a) a.1.isLt
  exact ha.1.trans h.symm

 def componentPortHeight (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base a : Dart (Fin g.edges.length)) : ℝ := ((componentPortWord g hg bits base).idxOf a : ℝ)

 theorem componentPortHeight_strict (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base : Dart (Fin g.edges.length)) {a b : Dart (Fin g.edges.length)}
    (ha : a ∈ componentPortWord g hg bits base) (hb : b ∈ componentPortWord g hg bits base)
    (hkey : contourKey g bits (eraseDart a) < contourKey g bits (eraseDart b)) :
    componentPortHeight g hg bits base a < componentPortHeight g hg bits base b :=
  Nat.cast_lt.mpr (sorted_key_idxOf_lt _ _ (componentPortWord_key_sorted g hg bits base) ha hb hkey)

 theorem componentPortHeight_injective (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base : Dart (Fin g.edges.length)) :
    Function.Injective (fun a : {a : Dart (Fin g.edges.length) // a ∈ componentPortWord g hg bits base} =>
      componentPortHeight g hg bits base a.val) := by
  intro a b heq
  apply idxOf_mem_injective (componentPortWord g hg bits base)
  exact Nat.cast_injective heq

 theorem componentPortHeight_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (base a b c d : Dart (Fin g.edges.length))
    (ha : a ∈ componentPortWord g hg bits base) (hb : b ∈ componentPortWord g hg bits base)
    (hc : c ∈ componentPortWord g hg bits base) (hd : d ∈ componentPortWord g hg bits base)
    (hkey : PortNoncrossing (contourKey g bits (eraseDart a)) (contourKey g bits (eraseDart b))
      (contourKey g bits (eraseDart c)) (contourKey g bits (eraseDart d))) :
    PortNoncrossing (componentPortHeight g hg bits base a) (componentPortHeight g hg bits base b)
      (componentPortHeight g hg bits base c) (componentPortHeight g hg bits base d) := by
  let S := {a : Dart (Fin g.edges.length) // a ∈ componentPortWord g hg bits base}
  exact PortNoncrossing.map_with (fun a : S => contourKey g bits (eraseDart a.val))
    (fun a : S => componentPortHeight g hg bits base a.val)
    (fun {a b} h => componentPortHeight_strict g hg bits base a.property b.property h)
    (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) (c := ⟨c,hc⟩) (d := ⟨d,hd⟩) hkey

/-- Actual finite occurrence matching heights, ready for literal circle arcs. -/
theorem componentOccurrenceHeights_noninterleaving (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    (base : Dart (Fin g.edges.length)) (e f : Fin g.edges.length)
    (he : typedOutward g e ∈ componentPortWord g hg bits base)
    (hf : typedOutward g f ∈ componentPortWord g hg bits base) (hne : e≠f) :
    Noninterleaving
      (min (componentPortHeight g hg bits base (typedOutward g e)) (componentPortHeight g hg bits base (reversePerm _ (typedOutward g e))))
      (max (componentPortHeight g hg bits base (typedOutward g e)) (componentPortHeight g hg bits base (reversePerm _ (typedOutward g e))))
      (min (componentPortHeight g hg bits base (typedOutward g f)) (componentPortHeight g hg bits base (reversePerm _ (typedOutward g f))))
      (max (componentPortHeight g hg bits base (typedOutward g f)) (componentPortHeight g hg bits base (reversePerm _ (typedOutward g f)))) := by
  have he' := (mem_componentPortWord g hg bits base _).mp he
  have hf' := (mem_componentPortWord g hg bits base _).mp hf
  simp only [dartHost_typedOutward,typedOutward_index] at he' hf'
  have hkey := nonTree_port_key_noncrossing g hg bits hLR halign e.isLt f.isLt he'.2 hf'.2
    (fun h => hne (Fin.ext h)) (he'.1.symm.trans hf'.1)
  have hmemE := componentPortWord_reverse_mem g hg bits base he
  have hmemF := componentPortWord_reverse_mem g hg bits base hf
  have hraw : PortNoncrossing (contourKey g bits (eraseDart (typedOutward g e)))
      (contourKey g bits (eraseDart (reversePerm _ (typedOutward g e))))
      (contourKey g bits (eraseDart (typedOutward g f)))
      (contourKey g bits (eraseDart (reversePerm _ (typedOutward g f)))) := by
    simpa only [erase_typedOutward,erase_reversePerm] using hkey
  exact componentPortHeight_noncrossing g hg bits base _ _ _ _ he hmemE hf hmemF hraw

end PlanarHom.PlanarityLRRealization
