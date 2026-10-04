import PlanarHom.TypedSideSwap

/-! NEW RECONSTRUCTION regression suite: concrete raw reserved-label movement,
ordinary companions, loops, repeated occurrences, an isolate, unequal and empty
sides, arbitrary original fields, all raw words, and contextual quantification. -/
noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.FiniteLabelLookupMachines
open PlanarHom.TypedBipartiteContext
open PlanarHom.AlgebraicProductInterpolation PlanarHom.AlgebraicProductInterpolation.RealLanguage
namespace PlanarHom.TypedCoordinateTransportRegressions

/-- Vertex 2 is isolated; edge 0 is repeated and the middle edge is a loop. -/
def sample : MixedCode :=
  ⟨3, [(0,1,0), (1,1,1), (0,1,0)], [(0,0), (1,1), (1,0)]⟩

def assignment : Fin sample.vertices → Fin 2 := ![0,1,0]

theorem sample_valid : sample.Valid 2 2 := by norm_num [MixedCode.Valid, sample]

/-- Both ordinary unary labels stay fixed. Only intrinsic labels 2 and 3 swap. -/
theorem concrete_reserved_swap :
    (withDomains (unaryTypes:=2) sample assignment).relabelUnary
      (finTable (liftDomainAlias swapDomains 2)) =
    ⟨3, [(0,1,0), (1,1,1), (0,1,0)],
      [(0,0), (1,1), (1,0), (0,3), (1,2), (2,3)]⟩ := by decide

theorem ordinary_zero_fixed : liftDomainAlias swapDomains 2 (0 : Fin 4) = 0 := by decide

theorem ordinary_one_fixed : liftDomainAlias swapDomains 2 (1 : Fin 4) = 1 := by decide

/-- No original graph data are lost by a domain-coordinate roundtrip. -/
theorem domain_roundtrip {a b bt ut : ℕ} (ρ : Fin a ≃ Fin b)
    (g : MixedCode) (hg : g.Valid bt ut) (δ : Fin g.vertices → Fin a) :
    ((withDomains (unaryTypes:=ut) g δ).relabelUnary
      (finTable (liftDomainAlias ρ ut))).relabelUnary
      (finTable (liftDomainAlias ρ.symm ut)) = withDomains (unaryTypes:=ut) g δ := by
  rw [relabelDomains_withDomains ρ g hg δ,
    relabelDomains_withDomains ρ.symm g hg (ρ ∘ δ)]
  have h : ρ.symm ∘ (ρ ∘ δ) = δ := by funext v; exact ρ.symm_apply_apply (δ v)
  rw [h]

example : (fun d => swapColors 2 3 ⁻¹' domains 2 3 (swapDomains d)) = domains 3 2 :=
  swapColors_domains

example : (fun d => swapColors 0 3 ⁻¹' domains 0 3 (swapDomains d)) = domains 3 0 :=
  swapColors_domains

section OriginalField
variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}
variable (basis : Module.Basis (Fin dimension) ℚ K)
variable (M : Fin 3 → Matrix (Fin (2+3)) (Fin (2+3)) K)
variable (U : Fin 2 → Fin (2+3) → K) (w : Fin (2+3) → K)
variable (D : Fin 2 → Set (Fin (2+3)))
variable (B : Fin 3 → Fin 2 → Fin 2 → Prop) (T : Fin 2 → Fin 2 → Prop)

/-- This compares actual field-coded output functions on *every* raw input,
without reducing to semantic values or assuming canonical graph encodings. -/
theorem arbitrary_raw_field_codes :
    evaluationValue basis (fun l i j => M l (swapColors 2 3 i) (swapColors 2 3 j))
      (fun l i => U l (swapColors 2 3 i)) (fun i => w (swapColors 2 3 i)) =
      evaluationValue basis M U w :=
  evaluationValue_reindexColors basis (swapColors 2 3) M U w

/-- Arbitrary three-matrix/two-unary context and ordered policies in the original
field, including a real nonadaptive machine proof rather than a supplied map. -/
def arbitrary_companion_reduction :
    PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis M U w (D ∘ swapDomains)
        (fun l a b => B l (swapDomains a) (swapDomains b))
        (fun l a => T l (swapDomains a)))
      (domainEvaluationProblem basis M U w D B T) :=
  domainReindexReduction basis swapDomains M U w D _ B _ T
    (fun _ _ _ h => h) (fun _ _ h => h)

end OriginalField

/-- The resulting availability retains universal quantification over matrix and
unary contexts; unequal side sizes are not silently identified. -/
example {s : ℕ} (F : Fin s → Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (FB : Fin s → Fin 2 → Fin 2 → Prop)
    (N : Matrix (Fin (2+3)) (Fin (2+3)) ℝ)
    (h : TypedContextuallyAvailable (domains 2 3) F FB N sameY) :
    TypedContextuallyAvailable (domains 3 2)
      (fun l i j => F l (swapColors 2 3 i) (swapColors 2 3 j))
      (fun l a b => FB l (swapDomains a) (swapDomains b))
      (fun i j => N (swapColors 2 3 i) (swapColors 2 3 j)) sameX := by
  have hs := typed_contextual_side_swap F FB N sameY h
  rw [swapDomains_sameY] at hs
  exact hs

end PlanarHom.TypedCoordinateTransportRegressions
