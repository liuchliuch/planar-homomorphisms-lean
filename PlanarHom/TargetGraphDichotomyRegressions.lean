import PlanarHom.TargetGraphDichotomy


/-! Dedicated whole-source and raw-code boundary regressions. All numerical
checks use kernel reduction, with no native_decide certificate or axiom. -/
noncomputable section
open Classical
namespace PlanarHom.TargetGraphDichotomy.Regressions
open Complexity ZeroOneBasicStructure ZeroOneBasicTractability
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

def loopedClique (q : ℕ) : Target q := ⟨fun _ _ => true, fun _ _ => rfl⟩
def isolated : Target 1 := ⟨fun _ _ => false, fun _ _ => rfl⟩
def emptyTarget : Target 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩
def triangleTarget : Target 3 := ⟨fun i j => decide (i ≠ j), by intro i j; simp [ne_comm]⟩

theorem loopedClique_basic (q : ℕ) : (loopedClique q).Basic := by
  intro c
  exact Or.inl ⟨c.nonempty_supp.to_subtype, fun _ _ => rfl⟩

theorem isolated_basic : isolated.Basic := by
  intro c
  exact Or.inr (Or.inr ⟨c.nonempty_supp.to_subtype, inferInstance, fun _ _ => rfl⟩)

theorem empty_basic : emptyTarget.Basic := by
  intro c
  obtain ⟨i, _⟩ := c.nonempty_supp
  exact i.elim0

example (q : ℕ) : (loopedClique q).generalProblem.InFP :=
  (loopedClique q).general_inFP (loopedClique_basic q)
example : isolated.generalProblem.InFP := isolated.general_inFP isolated_basic
example : emptyTarget.generalProblem.InFP := emptyTarget.general_inFP empty_basic
example : emptyTarget.planarProblem.InFP := emptyTarget.planar_inFP empty_basic

-- Both bipartition fibers are nonempty, with unequal sizes two and one.
def side : Fin 3 → Bool := ![false, false, true]
theorem side_surjective : Function.Surjective side := by
  intro b
  cases b
  · exact ⟨0, rfl⟩
  · exact ⟨2, rfl⟩
example : ComponentBasic (fun i j => decide (side i ≠ side j)) :=
  Or.inr (Or.inl ⟨side, side_surjective, fun _ _ => rfl⟩)
example : FieldBasicZeroOneComponent (fun i j =>
    if decide (side i ≠ side j) then (1 : ℚ) else 0) :=
  (componentBasic_iff_matrix _).mp (Or.inr (Or.inl ⟨side, side_surjective, fun _ _ => rfl⟩))

-- Source graph forms really reject a loopless triangle.
theorem triangle_not_component_basic :
    ¬ComponentBasic triangleTarget.adjacent := by
  rintro (⟨_, hone⟩ | ⟨s, _, hs⟩ | ⟨_, hsub, _⟩)
  · have h := hone 0 0
    simp [triangleTarget] at h
  · have hn : ∀ i j : Fin 3, i ≠ j → s i ≠ s j := by
      intro i j hij
      have h := hs i j
      simpa [triangleTarget, hij] using h.symm
    have h01 := hn 0 1 (by decide)
    have h02 := hn 0 2 (by decide)
    have h12 := hn 1 2 (by decide)
    cases h0 : s 0 <;> cases h1 : s 1 <;> cases h2 : s 2 <;> simp_all
  · have h := hsub.elim (0 : Fin 3) 1
    exact (by decide : (0 : Fin 3) ≠ 1) h

-- Fixed weighted bipartite computation needs no planar input hypothesis.
def rationalBasis : Module.Basis (Fin 1) ℚ ℚ := Module.Basis.singleton (Fin 1) ℚ
def weights : Fin 3 → ℚ := ![2, 3, 7]
def k33 : MixedCode := ⟨6,
  [(0,3,0),(0,4,0),(0,5,0),(1,3,0),(1,4,0),(1,5,0),
   (2,3,0),(2,4,0),(2,5,0)], []⟩
theorem k33_valid : k33.Valid 1 0 := by simp [MixedCode.Valid, k33]
example : evaluateCode side weights k33 = 85750 := by
  rw [bipartite_evaluateCode_eq side weights k33 k33_valid]
  decide +kernel
example : evaluateCode side weights k33 =
    k33.evaluate k33_valid (fun _ : Fin 1 => bipartiteMatrix side)
      emptyUnaries weights :=
  bipartite_evaluateCode_eq side weights k33 k33_valid
example : (MixedCode.restrictedEvaluationProblem rationalBasis
    (fun _ : Fin 1 => bipartiteMatrix side) emptyUnaries
    weights (MixedCode.Valid 1 0)).InFP :=
  basic_valid_inFP rationalBasis _ weights
    (Or.inr (Or.inl ⟨side, side_surjective, fun _ _ => rfl⟩))

-- The exact same natural codec and actual total count are used in both regimes.
example (q : ℕ) (R : ZeroOneSharpPMembership.Relation q) (raw : Bits) :
    (unrestrictedProblem q R).value raw =
      (ZeroOneSharpPMembership.planarProblem q R).value raw := rfl
example (q : ℕ) (R : ZeroOneSharpPMembership.Relation q) :
    CountingMember (unrestrictedProblem q R) := unrestricted_membership q R
example (q : ℕ) (R : ZeroOneSharpPMembership.Relation q) :
    PromisePolyTimeTuringReduction (ZeroOneSharpPMembership.planarProblem q R)
      (unrestrictedProblem q R) := planar_from_unrestricted q R

def isolateInput : GraphCode := ⟨1, []⟩
def alternateIsolate : Bits := BitEncoding.frame [false] ++ GraphCode.edgeEncoding.encode []
theorem isolateInput_valid : isolateInput.Valid := by simp [GraphCode.Valid, isolateInput]
theorem alternate_decode : GraphCode.encoding.decode alternateIsolate = some isolateInput := by
  change ((BitEncoding.unaryNat.prod GraphCode.edgeEncoding).decode alternateIsolate).map
    (fun p => GraphCode.mk p.1 p.2) = some isolateInput
  simp [alternateIsolate, BitEncoding.prod, BitEncoding.unaryNat,
    GraphCode.edgeEncoding.decode_encode, isolateInput]
example : alternateIsolate ≠ GraphCode.encoding.encode isolateInput := by decide +kernel
example : (loopedClique 2).generalProblem.valid alternateIsolate :=
  ⟨isolateInput, alternate_decode, isolateInput_valid⟩
example : (loopedClique 2).generalProblem.value alternateIsolate = BitEncoding.nat.encode 2 := by
  rw [(loopedClique 2).general_value_decode alternateIsolate isolateInput alternate_decode isolateInput_valid]
  congr 1
  simp [ZeroOneSharpPMembership.count,ZeroOneSharpPMembership.Hom,
    ZeroOneSharpPMembership.IsHom,isolateInput,loopedClique]


-- All-q endpoint remains free of supplied classification/hardness/FP witnesses.
example {q : ℕ} (H : Target q) :
    (H.Basic → H.planarProblem.InFP ∧ H.generalProblem.InFP) ∧
    (¬H.Basic → CountingComplete H.planarProblem ∧ CountingComplete H.generalProblem) :=
  corollary121 H

end PlanarHom.TargetGraphDichotomy.Regressions
