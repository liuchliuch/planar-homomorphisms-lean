import PlanarHom.PlanarityLRConstraintBlocks

/-! NEW exact alignment compilation. The alignment-safety condition below is
an explicit structural property to be derived from DFS return/lowpoint data;
this module never assumes a planar embedding or a satisfying assignment. -/
namespace PlanarHom.PlanarityLRConstraintBlocks
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives PlanarityParitySolver

abbrev AlignmentPair := ℕ × ℕ
abbrev alignmentCode := natCode.prod natCode

def Occurs (blocks : List ForkBlock) (u : ℕ) : Prop :=
  ∃ B ∈ blocks, u ∈ B.1 ∨ u ∈ B.2

def relevant (blocks : List ForkBlock) (u : ℕ) : Bool :=
  blocks.any (fun B => decide (u ∈ B.1 ∨ u ∈ B.2))

theorem relevant_iff (blocks : List ForkBlock) (u : ℕ) : relevant blocks u = true ↔ Occurs blocks u := by
  simp [relevant,Occurs]

def Aligned (side : ℕ → Bool) (pairs : List AlignmentPair) : Prop :=
  ∀ p ∈ pairs, side p.1 = side p.2

/-- A pair is safe to align if either constrained endpoint is witnessed with
both endpoints on one side of a single actual fork block. -/
def AlignmentSafe (blocks : List ForkBlock) (pairs : List AlignmentPair) : Prop :=
  ∀ p ∈ pairs, (Occurs blocks p.1 ∨ Occurs blocks p.2) →
    ∃ B ∈ blocks, (p.1 ∈ B.1 ∧ p.2 ∈ B.1) ∨ (p.1 ∈ B.2 ∧ p.2 ∈ B.2)

def canonicalSide (blocks : List ForkBlock) (side : ℕ → Bool) : ℕ → Bool :=
  fun u => if relevant blocks u then side u else false

theorem canonicalSide_eq (blocks : List ForkBlock) (side : ℕ → Bool) {u : ℕ} (h : Occurs blocks u) :
    canonicalSide blocks side u = side u := by
  simp [canonicalSide,(relevant_iff blocks u).mpr h]

theorem canonicalSide_partition (blocks : List ForkBlock) (side : ℕ → Bool)
    (h : LRPartition side blocks) : LRPartition (canonicalSide blocks side) blocks := by
  intro B hB
  have hb := h B hB
  have hL (u : ℕ) (hu : u ∈ B.1) : canonicalSide blocks side u = side u :=
    canonicalSide_eq blocks side ⟨B,hB,Or.inl hu⟩
  have hR (u : ℕ) (hu : u ∈ B.2) : canonicalSide blocks side u = side u :=
    canonicalSide_eq blocks side ⟨B,hB,Or.inr hu⟩
  refine ⟨?_,?_,?_⟩
  · intro u hu v hv
    rw [hL u hu,hL v hv]
    exact hb.1 u hu v hv
  · intro u hu v hv
    rw [hR u hu,hR v hv]
    exact hb.2.1 u hu v hv
  · intro u hu v hv
    rw [hL u hu,hR v hv]
    exact hb.2.2 u hu v hv

theorem canonicalSide_aligned (blocks : List ForkBlock) (pairs : List AlignmentPair)
    (hsafe : AlignmentSafe blocks pairs) (side : ℕ → Bool) (h : LRPartition side blocks) :
    Aligned (canonicalSide blocks side) pairs := by
  intro p hp
  by_cases hocc : Occurs blocks p.1 ∨ Occurs blocks p.2
  · obtain ⟨B,hB,hmem⟩ := hsafe p hp hocc
    rcases hmem with hmem | hmem
    · rw [canonicalSide_eq blocks side ⟨B,hB,Or.inl hmem.1⟩,
        canonicalSide_eq blocks side ⟨B,hB,Or.inl hmem.2⟩]
      exact (h B hB).1 _ hmem.1 _ hmem.2
    · rw [canonicalSide_eq blocks side ⟨B,hB,Or.inr hmem.1⟩,
        canonicalSide_eq blocks side ⟨B,hB,Or.inr hmem.2⟩]
      exact (h B hB).2.1 _ hmem.1 _ hmem.2
  · have h₁ : relevant blocks p.1 ≠ true := fun hh => hocc (Or.inl ((relevant_iff _ _).mp hh))
    have h₂ : relevant blocks p.2 ≠ true := fun hh => hocc (Or.inr ((relevant_iff _ _).mp hh))
    simp [canonicalSide,h₁,h₂]

/-- Safe alignment never introduces a new satisfiability assumption. -/
theorem exists_aligned_iff (blocks : List ForkBlock) (pairs : List AlignmentPair)
    (hsafe : AlignmentSafe blocks pairs) :
    (∃ side, LRPartition side blocks ∧ Aligned side pairs) ↔ ∃ side, LRPartition side blocks := by
  constructor
  · rintro ⟨side,h,_⟩
    exact ⟨side,h⟩
  · rintro ⟨side,h⟩
    exact ⟨canonicalSide blocks side,canonicalSide_partition blocks side h,
      canonicalSide_aligned blocks pairs hsafe side h⟩

def alignedEquations (blocks : List ForkBlock) (pairs : List AlignmentPair) : List Constraint :=
  compile blocks ++ pairs.map (fun p => (p.1,p.2,false))

def decideAlignedBlocks (input : List ForkBlock × List AlignmentPair) : Bool × Assignment :=
  computed (alignedEquations input.1 input.2)

theorem alignedEquations_spec (blocks : List ForkBlock) (pairs : List AlignmentPair) (side : ℕ → Bool) :
    Satisfies side (alignedEquations blocks pairs) ↔ LRPartition side blocks ∧ Aligned side pairs := by
  rw [alignedEquations,satisfies_append,compile_spec]
  apply and_congr_right
  intro _
  constructor
  · intro h p hp
    exact (xor_false_iff _ _).mp (h _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  · intro h e he
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
    exact (xor_false_iff _ _).mpr (h p hp)

theorem decideAlignedBlocks_sound (input : List ForkBlock × List AlignmentPair)
    (h : (decideAlignedBlocks input).1 = true) :
    LRPartition (lookup (decideAlignedBlocks input).2) input.1 ∧
      Aligned (lookup (decideAlignedBlocks input).2) input.2 :=
  (alignedEquations_spec _ _ _).mp (computed_sound _ h)

theorem decideAlignedBlocks_complete (input : List ForkBlock × List AlignmentPair) :
    (decideAlignedBlocks input).1 = true ↔ ∃ side, LRPartition side input.1 ∧ Aligned side input.2 := by
  rw [decideAlignedBlocks,computed_complete]
  exact exists_congr (fun side => alignedEquations_spec _ _ side)

theorem decideAlignedBlocks_safe_complete (input : List ForkBlock × List AlignmentPair)
    (h : AlignmentSafe input.1 input.2) :
    (decideAlignedBlocks input).1 = true ↔ ∃ side, LRPartition side input.1 := by
  rw [decideAlignedBlocks_complete,exists_aligned_iff _ _ h]

/-- Complete encoded compilation, including the actual equality constraints. -/
theorem fp_decideAlignedBlocks :
    FP (blockCode.list.prod alignmentCode.list) (BitEncoding.bool.prod assignmentCode) decideAlignedBlocks := by
  have hfst := fp_fst natCode natCode
  have hsnd := fp_snd natCode natCode
  have hpair : FP alignmentCode constraintCode (fun p => (p.1,p.2,false)) :=
    hfst.pair (hsnd.pair (fp_const _ BitEncoding.bool false))
  have hL := (fp_fst blockCode.list alignmentCode.list).comp fp_compile
  have hR := (fp_snd blockCode.list alignmentCode.list).comp
    (ListMapMachines.fp_map alignmentCode constraintCode (fun p => (p.1,p.2,false)) hpair)
  exact (((hL.pair hR).comp (ListMutationMachines.fp_append constraintCode)).comp fp_computed)

end PlanarHom.PlanarityLRConstraintBlocks
