import PlanarHom.PlanarityLRAlignmentSafety

/-! NEW executable aligned LR decision and literal occurrence-indexed bit vector.
The computed output has the historical Bool×List Bool interface. Its proved
acceptance criterion is the raw-code combinatorial LR condition; the ordinary
planarity equivalence is not assumed by this module. -/
namespace PlanarHom.PlanarityLRConstraints
open Complexity PlanarityParitySolver PlanarityLRConstraintBlocks PlanarityLRRawConstraints

def decideAligned (g : MixedCode) : Bool × List Bool :=
  let out := solveAlignedLR g
  (out.1,(List.range g.edges.length).map (lookup out.2))

def bitSide (bits : List Bool) : ℕ → Bool := fun e => bits.getD e false

@[simp] theorem decideAligned_length (g : MixedCode) : (decideAligned g).2.length = g.edges.length := by
  simp [decideAligned]

theorem decideAligned_bit (g : MixedCode) {e : ℕ} (he : e < g.edges.length) :
    bitSide (decideAligned g).2 e = lookup (solveAlignedLR g).2 e := by
  simp [decideAligned,bitSide,List.getD_eq_getElem?_getD,he]

theorem lrCondition_congr (g : MixedCode) (f h : ℕ → Bool)
    (heq : ∀ e < g.edges.length, f e = h e) (hf : LRCondition g f) : LRCondition g h := by
  intro v hv hheight e₁ he₁ e₂ he₂ hne
  have H := hf v hv hheight e₁ he₁ e₂ he₂ hne
  have hL (b : ℕ) (hb : b ∈ (forkBlock g e₁ e₂).1) : f b = h b :=
    heq b (returns_valid g e₁ (List.mem_filter.mp hb).1)
  have hR (b : ℕ) (hb : b ∈ (forkBlock g e₁ e₂).2) : f b = h b :=
    heq b (returns_valid g e₂ (List.mem_filter.mp hb).1)
  refine ⟨?_,?_,?_⟩
  · intro b hb c hc
    rw [← hL b hb,← hL c hc]
    exact H.1 b hb c hc
  · intro b hb c hc
    rw [← hR b hb,← hR c hc]
    exact H.2.1 b hb c hc
  · intro b hb c hc
    rw [← hL b hb,← hR c hc]
    exact H.2.2 b hb c hc

theorem alignment_congr (g : MixedCode) (f h : ℕ → Bool)
    (heq : ∀ e < g.edges.length, f e = h e) (hf : Aligned f (alignmentPairs g)) :
    Aligned h (alignmentPairs g) := by
  intro p hp
  rcases p with ⟨b,c⟩
  obtain ⟨e,_,hb,hc,_,_⟩ := (mem_alignmentPairs g b c).mp hp
  rw [← heq b (returns_valid g e hb),← heq c (returns_valid g e hc)]
  exact hf (b,c) hp

/-- Successful actual output is an aligned LR partition on original occurrence
indices, including the exact bit-vector lookup convention. -/
theorem decideAligned_sound (g : MixedCode) (h : (decideAligned g).1 = true) :
    LRCondition g (bitSide (decideAligned g).2) ∧
      Aligned (bitSide (decideAligned g).2) (alignmentPairs g) := by
  have H := solveAlignedLR_sound g h
  exact ⟨lrCondition_congr g _ _ (fun e he => (decideAligned_bit g he).symm) H.1,
    alignment_congr g _ _ (fun e he => (decideAligned_bit g he).symm) H.2⟩

/-- Alignment does not strengthen the combinatorial acceptance condition. -/
theorem decideAligned_complete (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) :
    (decideAligned g).1 = true ↔ ∃ side, LRCondition g side := solveAlignedLR_complete g hg

end PlanarHom.PlanarityLRConstraints
