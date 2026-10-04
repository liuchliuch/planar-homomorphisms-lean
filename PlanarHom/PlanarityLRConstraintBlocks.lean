import PlanarHom.PlanarityParityPolynomial

/-!
# NEW exact LR fork-block parity compilation

A fork block consists of the two return-edge groups that must each occupy one
side and, when both groups are nonempty, opposite sides. This module compiles
those literal groups into Boolean parity equations and computes a verified
assignment in FP. Deriving these groups from an actual DFS-oriented graph and
proving geometric planarity remain separate obligations.
-/
namespace PlanarHom.PlanarityLRConstraintBlocks
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open PlanarityParitySolver

abbrev ForkBlock := List ℕ × List ℕ
abbrev blockCode := natCode.list.prod natCode.list
abbrev crossingCode := natCode.list.prod (natCode.list.prod BitEncoding.bool)

def crossEquations (xs ys : List ℕ) (b : Bool) : List Constraint :=
  xs.flatMap (fun u => ys.map (fun v => (u,v,b)))

def equations (block : ForkBlock) : List Constraint :=
  crossEquations block.1 block.1 false ++ crossEquations block.2 block.2 false ++
    crossEquations block.1 block.2 true

def compile (blocks : List ForkBlock) : List Constraint := blocks.flatMap equations

def Monochromatic (f : ℕ → Bool) (xs : List ℕ) : Prop := ∀ u ∈ xs, ∀ v ∈ xs, f u = f v

def ForkHolds (f : ℕ → Bool) (block : ForkBlock) : Prop :=
  Monochromatic f block.1 ∧ Monochromatic f block.2 ∧
    ∀ u ∈ block.1, ∀ v ∈ block.2, f u ≠ f v

def LRPartition (f : ℕ → Bool) (blocks : List ForkBlock) : Prop := ∀ block ∈ blocks, ForkHolds f block

def decideBlocks (blocks : List ForkBlock) : Bool × Assignment := computed (compile blocks)

theorem crossEquations_spec (f : ℕ → Bool) (xs ys : List ℕ) (b : Bool) :
    Satisfies f (crossEquations xs ys b) ↔ ∀ u ∈ xs, ∀ v ∈ ys, Bool.xor (f u) (f v) = b := by
  constructor
  · intro h u hu v hv
    exact h (u,v,b) (List.mem_flatMap.mpr ⟨u,hu,List.mem_map.mpr ⟨v,hv,rfl⟩⟩)
  · intro h e he
    obtain ⟨u,hu,he⟩ := List.mem_flatMap.mp he
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp he
    exact h u hu v hv

theorem xor_false_iff (a b : Bool) : Bool.xor a b = false ↔ a = b := by cases a <;> cases b <;> decide

theorem xor_true_iff (a b : Bool) : Bool.xor a b = true ↔ a ≠ b := by cases a <;> cases b <;> decide

theorem satisfies_append (f : ℕ → Bool) (es fs : List Constraint) :
    Satisfies f (es++fs) ↔ Satisfies f es ∧ Satisfies f fs := by
  constructor
  · intro h
    exact ⟨fun e he => h e (List.mem_append_left fs he),fun e he => h e (List.mem_append_right es he)⟩
  · rintro ⟨he,hf⟩ e hem
    exact (List.mem_append.mp hem).elim (he e) (hf e)

/-- No pairwise constraint is lost, including conflicting repeated occurrence labels. -/
theorem equations_spec (f : ℕ → Bool) (block : ForkBlock) :
    Satisfies f (equations block) ↔ ForkHolds f block := by
  simp only [equations,satisfies_append,crossEquations_spec,xor_false_iff,xor_true_iff,
    ForkHolds,Monochromatic]
  exact and_assoc

theorem compile_spec (f : ℕ → Bool) (blocks : List ForkBlock) :
    Satisfies f (compile blocks) ↔ LRPartition f blocks := by
  constructor
  · intro h block hb
    apply (equations_spec f block).mp
    intro e he
    exact h e (List.mem_flatMap.mpr ⟨block,hb,he⟩)
  · intro h e he
    obtain ⟨block,hb,he⟩ := List.mem_flatMap.mp he
    exact (equations_spec f block).mpr (h block hb) e he

/-- A successful output is a literal valid LR partition of every supplied fork block. -/
theorem decideBlocks_sound (blocks : List ForkBlock) (h : (decideBlocks blocks).1 = true) :
    LRPartition (lookup (decideBlocks blocks).2) blocks :=
  (compile_spec _ blocks).mp (computed_sound _ h)

/-- The actual decision is complete for the exact fork-block condition. -/
theorem decideBlocks_complete (blocks : List ForkBlock) :
    (decideBlocks blocks).1 = true ↔ ∃ f, LRPartition f blocks := by
  rw [decideBlocks,computed_complete]
  exact exists_congr (fun f => compile_spec f blocks)

theorem crossEquations_length (xs ys : List ℕ) (b : Bool) :
    (crossEquations xs ys b).length = xs.length*ys.length := by
  induction xs with
  | nil => simp [crossEquations]
  | cons u xs ih => simp [crossEquations,ih,Nat.add_mul,Nat.add_comm]

theorem equations_length (block : ForkBlock) :
    (equations block).length = block.1.length^2+block.2.length^2+block.1.length*block.2.length := by
  simp [equations,crossEquations_length,pow_two,Nat.add_assoc]

/-- A complete ordinary-machine Cartesian product of literal labels. -/
theorem fp_crossEquations : FP crossingCode constraintCode.list
    (fun p => crossEquations p.1 p.2.1 p.2.2) := by
  let context := natCode.prod BitEncoding.bool
  have hctx := fp_fst context natCode
  have hu := hctx.comp (fp_fst natCode BitEncoding.bool)
  have hb := hctx.comp (fp_snd natCode BitEncoding.bool)
  have hv := fp_snd context natCode
  have htuple : FP (context.prod natCode) constraintCode (fun p => (p.1.1,p.2,p.1.2)) :=
    hu.pair (hv.pair hb)
  have hrow := ListContextMachines.fp_mapWithContext context natCode constraintCode
    (fun p => (p.1.1,p.2,p.1.2)) htuple
  let rowInput := (natCode.list.prod BitEncoding.bool).prod natCode
  have hrowctx := fp_fst (natCode.list.prod BitEncoding.bool) natCode
  have hxs := hrowctx.comp (fp_fst natCode.list BitEncoding.bool)
  have hb' := hrowctx.comp (fp_snd natCode.list BitEncoding.bool)
  have hu' := fp_snd (natCode.list.prod BitEncoding.bool) natCode
  have hrow' : FP rowInput constraintCode.list
      (fun p => p.1.1.map (fun v => (p.2,v,p.1.2))) := ((hu'.pair hb').pair hxs).comp hrow
  have hrows := ListContextMachines.fp_mapWithContext (natCode.list.prod BitEncoding.bool)
    natCode constraintCode.list (fun p => p.1.1.map (fun v => (p.2,v,p.1.2))) hrow'
  have hs := (fp_snd natCode.list (natCode.list.prod BitEncoding.bool)).pair
    (fp_fst natCode.list (natCode.list.prod BitEncoding.bool))
  exact ((hs.comp hrows).comp (ListFlattenMachines.fp_flatten constraintCode)).congr
    (fun p => by simp [crossEquations,List.flatMap_def])

theorem fp_equations : FP blockCode constraintCode.list equations := by
  have hL := fp_fst natCode.list natCode.list
  have hR := fp_snd natCode.list natCode.list
  have hfalse := fp_const blockCode BitEncoding.bool false
  have htrue := fp_const blockCode BitEncoding.bool true
  have hLL := (hL.pair (hL.pair hfalse)).comp fp_crossEquations
  have hRR := (hR.pair (hR.pair hfalse)).comp fp_crossEquations
  have hLR := (hL.pair (hR.pair htrue)).comp fp_crossEquations
  exact (((hLL.pair hRR).comp (ListMutationMachines.fp_append constraintCode)).pair hLR).comp
    (ListMutationMachines.fp_append constraintCode)

theorem fp_compile : FP blockCode.list constraintCode.list compile := by
  exact ((ListMapMachines.fp_map blockCode constraintCode.list equations fp_equations).comp
    (ListFlattenMachines.fp_flatten constraintCode)).congr
    (fun blocks => by simp [compile,List.flatMap_def])

/-- Total polynomial-time LR fork-block decision with an actual assignment witness. -/
theorem fp_decideBlocks : FP blockCode.list (BitEncoding.bool.prod assignmentCode) decideBlocks :=
  fp_compile.comp fp_computed

end PlanarHom.PlanarityLRConstraintBlocks
