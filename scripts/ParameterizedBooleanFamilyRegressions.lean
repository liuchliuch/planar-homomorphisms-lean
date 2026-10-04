import PlanarHom.BooleanParameterRealAvailability
import PlanarHom.BooleanFamilyPosDef

noncomputable section
open Classical
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.FiniteLanguageAliases

private def edgeLoop : MixedCode := ⟨2,[(0,0,1),(0,1,1)],[]⟩
private theorem edgeLoop_valid : edgeLoop.Valid 2 0 := by simp [edgeLoop,Valid]
private def edgeless : MixedCode := ⟨1,[],[]⟩
private theorem edgeless_valid : edgeless.Valid 2 0 := by simp [edgeless,Valid]

-- Scaling counts both a genuine loop occurrence and a distinct nonloop edge.
example (M : Fin 1→Matrix (Fin 1) (Fin 1) ℚ) (A : Matrix (Fin 1) (Fin 1) ℚ)
    (w : Fin 1→ℚ) :
    edgeLoop.evaluate edgeLoop_valid (appendOne M ((-2 : ℚ) • A)) (fun u : Fin 0=>Fin.elim0 u) w=
      4*edgeLoop.evaluate edgeLoop_valid (appendOne M A) (fun u : Fin 0=>Fin.elim0 u) w := by
  simpa [edgeLoop,markedCount] using SelectedScalarSemantics.evaluate_append_smul
    edgeLoop edgeLoop_valid M A (fun u : Fin 0=>Fin.elim0 u) w (-2)

example (M : Fin 1→Matrix (Fin 1) (Fin 1) ℚ) (A : Matrix (Fin 1) (Fin 1) ℚ)
    (w : Fin 1→ℚ) :
    edgeLoop.evaluate edgeLoop_valid (appendOne M ((0 : ℚ) • A)) (fun u : Fin 0=>Fin.elim0 u) w=0 := by
  simpa [edgeLoop,markedCount] using SelectedScalarSemantics.evaluate_append_smul
    edgeLoop edgeLoop_valid M A (fun u : Fin 0=>Fin.elim0 u) w 0

-- The empty selected product is 1, even when the known scalar is zero.
example (M : Fin 1→Matrix (Fin 1) (Fin 1) ℚ) (A : Matrix (Fin 1) (Fin 1) ℚ)
    (w : Fin 1→ℚ) :
    edgeless.evaluate edgeless_valid (appendOne M ((0 : ℚ) • A)) (fun u : Fin 0=>Fin.elim0 u) w=
      edgeless.evaluate edgeless_valid (appendOne M A) (fun u : Fin 0=>Fin.elim0 u) w := by
  simpa [edgeless,markedCount] using SelectedScalarSemantics.evaluate_append_smul
    edgeless edgeless_valid M A (fun u : Fin 0=>Fin.elim0 u) w 0

example : edgeLoop.expandBinaryWords (FiniteLabelWordLookupMachines.finTable
    (ParameterizedAppendSchurReduction.words 1))=
      (⟨2,[(0,0,1),(0,0,2),(0,1,1),(0,1,2)],[]⟩ : MixedCode) := by decide

-- Prescribed domains are the exact same vertex records through the parallel query.
example {d : ℕ} (δ : Fin edgeLoop.vertices→Fin d) :
    (PrescribedDomains.withDomains (unaryTypes:=0) edgeLoop δ).expandBinaryWords
      (FiniteLabelWordLookupMachines.finTable (ParameterizedAppendSchurReduction.words 1))=
    PrescribedDomains.withDomains (unaryTypes:=0)
      (edgeLoop.expandBinaryWords (FiniteLabelWordLookupMachines.finTable
        (ParameterizedAppendSchurReduction.words 1))) δ := rfl

-- Canonical rational parameter words accompany arbitrary successful raw graph encodings.
example {X K : Type} [Field K] [Algebra ℚ K] {n q b u : ℕ}
    (basis : Module.Basis (Fin n) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K) (w : Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (raw : Bits) :
    (ParameterizedMatrixEvaluation.problem basis ex M U w F allowed).valid raw ↔
      ∃x rawGraph,raw=BitEncoding.frame (ex.encode x)++rawGraph ∧ allowed x ∧
        PlanarInput (b+1) u rawGraph :=
  ParameterizedMatrixEvaluation.valid_iff_rawGraph basis ex M U w F allowed raw

#print axioms EndpointLoopParameterAvailability.fp_family
#print axioms EndpointLoopParameterAvailability.reduction
#print axioms DomainEndpointLoopParameterAvailability.reduction_of_pathTyping
#print axioms DomainEndpointLoopParameterAvailability.reduction_global
#print axioms ParameterizedScalarReduction.reduction
#print axioms ParameterizedAppendSchurReduction.reduction

-- A zero-dimensional Boolean tensor has one color: normalization gives1,
-- for every exponent and parameter, with no empty-color reinterpretation.
example {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K] (γ : K) (hγ : γ≠0)
    (k : ℕ) (x : ℚ) :
    EndpointLoopParameterAvailability.family (fun _ _ : Fin 1=>γ) k ((γ^(2*k+1))⁻¹) x 0 0=1 := by
  simp only [EndpointLoopParameterAvailability.family,EndpointLoopMachines.decorated,
    DistanceKernelEvaluationMachines.matrix,SimpleGraph.dist_self,pow_zero,mul_one]
  rw [show 2*k+1=k+1+k by omega,pow_add,pow_add,pow_one]
  exact inv_mul_cancel₀ (mul_ne_zero (mul_ne_zero (pow_ne_zero k hγ) hγ) (pow_ne_zero k hγ))

#print axioms AlgebraicProductInterpolation.RealLanguage.booleanFamilyReduction
#print axioms AlgebraicProductInterpolation.RealLanguage.domainBooleanFamilyReduction
#print axioms AlgebraicProductInterpolation.RealLanguage.booleanFamily_matrix_real
