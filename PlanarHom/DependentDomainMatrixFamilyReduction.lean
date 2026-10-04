import PlanarHom.RestrictedDependentMatrixFamilyReduction
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.MixedEvaluationFieldMap

/-! Variable-field family transfer on the exact encoded prescribed-domain graph promise. -/
noncomputable section
namespace PlanarHom.DependentDomainMatrixFamilyReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PrescribedDomains
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)] [∀ x, DecidableEq (K x)]
variable {sourceDimension q bt ut dt : ℕ}

def targetProblem (ex : BitEncoding X) (dimension : X → ℕ)
    (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x)) (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop) : PromiseProblem :=
  RestrictedDependentMatrixFamilyReduction.targetProblem K ex (fun x => numberFieldEncoding (basis x))
    inclusion M (extendedUnaries U D) w B allowed (EncodedGraph policy typing)

/-- Every successfully decoded original graph word with its exact domain metadata
is admitted; no canonical-graph-word restriction is introduced. -/
theorem valid_iff_rawGraph (ex : BitEncoding X) (dimension : X → ℕ)
    (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x)) (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop) (raw : Bits) :
    (targetProblem K ex dimension basis inclusion M U w D policy typing B allowed).valid raw ↔
      ∃ x rawGraph, raw = BitEncoding.frame (ex.encode x) ++ rawGraph ∧ allowed x ∧
        EncodedInput policy typing rawGraph := by
  constructor
  · rintro ⟨⟨x,g⟩,hword,hx,hg⟩
    exact ⟨x,g.val,hword.symm,hx,(encodedInput_iff_graph policy typing _).mpr ⟨g.value,g.decode_raw,hg⟩⟩
  · rintro ⟨x,rawGraph,hword,hx,hg⟩
    obtain ⟨g,hd,hg⟩ := (encodedInput_iff_graph policy typing _).mp hg
    let gw : BitEncoding.ValidWord encoding := ⟨rawGraph,⟨g,hd⟩⟩
    refine ⟨(x,gw),hword.symm,hx,?_⟩
    have he : gw.value = g := BitEncoding.ValidWord.value_eq (w := gw) hd
    change EncodedGraph policy typing gw.value
    rw [he]
    exact hg

/-- Intrinsic domain indicators remain the same 0/1 values after field inclusion;
the target uses the original domain sets and their exact encoded records. -/
theorem value_raw_input (ex : BitEncoding X) (dimension : X → ℕ)
    (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x)) (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (p : X × BitEncoding.ValidWord MixedCode.encoding) :
    (targetProblem K ex dimension basis inclusion M U w D policy typing B allowed).value
      ((DependentMatrixEvaluation.inputEncoding ex).encode p) =
      (numberFieldEncoding (basis p.1)).encode (totalEvaluation
        (appendOne (fun l i j => inclusion p.1 (M l i j)) (B p.1))
        (extendedUnaries (fun l i => inclusion p.1 (U l i)) D)
        (fun i => inclusion p.1 (w i)) p.2.value) := by
  have h := DependentMatrixEvaluation.value_raw_input K ex (fun x => numberFieldEncoding (basis x))
    inclusion M (extendedUnaries U D) w B allowed p
  simpa only [DependentMatrixEvaluation.answer, map_extendedUnaries] using h

/-- The generic semantic predicate obligations are discharged by the existing
encoded-domain thickening and validity theorems. Original domain records persist. -/
def reduction
    (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L) (ex : BitEncoding X)
    (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
    (inclusion : ∀ x, L →+* K x)
    (M : Fin bt → Matrix (Fin q) (Fin q) L) (U : Fin ut → Fin q → L) (w : Fin q → L)
    (D : Fin dt → Set (Fin q)) (policy : Fin (bt+1) → Fin dt → Fin dt → Prop)
    (typing : Fin ut → Fin dt → Prop)
    (F : ℕ → Matrix (Fin q) (Fin q) L) (B : ∀ x, Matrix (Fin q) (Fin q) (K x)) (allowed : X → Prop)
    (n₀ : ℕ) (hn₀ : 1 ≤ n₀) (candidates : Polynomial ℕ)
    (degreeBound : ℕ) (degree_le : ∀ x, dimension x ≤ degreeBound)
    (hpresentation : FP ex BitEncoding.rat.list
      (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
    (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
    (hadd : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun s : Σ x, K x × K x => ⟨s.1,s.2.1+s.2.2⟩))
    (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
      (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
      (fun p => ⟨p.1,inclusion p.1 p.2⟩))
    (hF : FP BitEncoding.unaryNat ((numberFieldEncoding sourceBasis).vector (q*q))
      (fun n => binaryAlphabet (F n)))
    (hB : FP ex (DependentFieldCodecs.sigma ex
      (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector (q*q)))
      (fun x => ⟨x,binaryAlphabet (B x)⟩))
    (hNonzero : ∀ n, n₀ ≤ n → ∀ i j, F n i j ≠ 0)
    (hSample : ∀ x, allowed x → ∀ m, ∃ j < candidates.eval m,
      SourceExponentRepresentatives.CrossCompatibleAt (binaryAlphabet (F (n₀+j))) (binaryAlphabet (B x)) m)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction (RestrictedMatrixFamilyReduction.sourceProblem sourceBasis M (extendedUnaries U D) w F (EncodedGraph policy typing)) base) :
    PromisePolyTimeTuringReduction
      (targetProblem K ex dimension basis inclusion M U w D policy typing B allowed) base :=
  RestrictedDependentMatrixFamilyReduction.canonicalReduction K sourceBasis ex dimension basis inclusion
    M (extendedUnaries U D) w F B allowed (EncodedGraph policy typing)
    (fun _ h => (h.planarValid policy typing).1) (fun _ h s => h.parallelLabel policy typing bt s)
    n₀ hn₀ candidates degreeBound degree_le hpresentation hmul hadd hinclusion hF hB hNonzero hSample base simulation

end PlanarHom.DependentDomainMatrixFamilyReduction
