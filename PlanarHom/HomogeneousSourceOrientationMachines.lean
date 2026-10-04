import PlanarHom.HomogeneousSourceOrientationSemantics
import PlanarHom.RootedQueryMachines
import PlanarHom.RootedRestrictionReduction
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.ListDecompositionMachines

/-! Literal input preparation for homogeneous typed source orientation.
The domain tag is read from serialized input metadata, never chosen from a
proof of the input promise. Erasure retains the actual vertices and every
binary occurrence. Both fixed root-side attachment lists are actual FP
programs, and only the list selected by the input's root tag is queried. -/
noncomputable section
namespace PlanarHom.HomogeneousSourceOrientation
open Complexity Complexity.MixedCode PrescribedDomains TypedBipartiteContext
open PairProjectionMachines ArithmeticCircuitPrimitives

abbrev sidePolicies : Fin 1 → Fin 2 → Fin 2 → Prop := fun _ => crossPolicy
abbrev emptyPolicies : Fin 0 → Fin 2 → Prop := fun l => l.elim0

/-- Remove the intrinsic domain records, retaining every binary occurrence. -/
def eraseDomains (g : MixedCode) : MixedCode := ⟨g.vertices, g.edges, []⟩

/-- The first domain record belongs to vertex zero on every promised input. -/
def rootSide (g : MixedCode) : Bool := decide ((g.unaries.headD (0,0)).2 = 1)

@[simp] theorem eraseDomains_vertices (g : MixedCode) : (eraseDomains g).vertices = g.vertices := rfl
@[simp] theorem eraseDomains_edges (g : MixedCode) : (eraseDomains g).edges = g.edges := rfl
@[simp] theorem eraseDomains_support (g : MixedCode) :
    GraphComponentCode.support (eraseDomains g) = GraphComponentCode.support g := rfl
@[simp] theorem eraseDomains_underlying (g : MixedCode) :
    (eraseDomains g).underlying = g.underlying := rfl

@[simp] theorem eraseDomains_withDomains (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) : eraseDomains (withDomains (unaryTypes := 0) g δ) = g := by
  cases g with
  | mk n es us =>
    have hu := unaries_nil_of_valid_zero ⟨n,es,us⟩ hg
    simp only [MixedCode.unaries] at hu
    subst us
    rfl

theorem rootSide_withDomains (g : MixedCode) (hg : g.Valid 1 0)
    (δ : Fin g.vertices → Fin 2) (hn : 0 < g.vertices) :
    rootSide (withDomains (unaryTypes := 0) g δ) = decide (δ ⟨0,hn⟩ = 1) := by
  unfold rootSide withDomains
  rw [unaries_nil_of_valid_zero g hg]
  simp only [List.nil_append, domainOccurrences, Nat.zero_add]
  have hne : List.ofFn (fun v : Fin g.vertices => (v.val, (δ v).val)) ≠ [] := by
    intro h
    have hh := congrArg List.length h
    simp only [List.length_ofFn, List.length_nil] at hh
    omega
  have hhead : ∀ (xs : List (ℕ × ℕ)) (h : xs ≠ []), xs.headD (0,0) = xs.head h := by
    intro xs h
    cases xs with
    | nil => exact False.elim (h rfl)
    | cons a as => rfl
  rw [hhead _ hne, List.head_ofFn hne]
  congr 1
  apply propext
  constructor
  · exact fun h => Fin.ext h
  · exact fun h => congrArg Fin.val h

theorem fp_eraseDomains : FP MixedCode.encoding MixedCode.encoding eraseDomains := by
  exact (MixedCode.fp_vertices.pair
    (MixedCode.fp_edges.pair (fp_const MixedCode.encoding
      (BitEncoding.nat.prod BitEncoding.nat).list []))).transportOutput (fun _ => rfl)

theorem fp_rootSide : FP MixedCode.encoding BitEncoding.bool rootSide := by
  have hhead := MixedCode.fp_unaries.comp
    (ListDecompositionMachines.fp_headD (BitEncoding.nat.prod BitEncoding.nat) (0,0))
  have hlabel := hhead.comp (fp_snd BitEncoding.nat BitEncoding.nat)
  exact (hlabel.pair (fp_const _ BitEncoding.nat 1)).comp NatListSumMachines.fp_equal

/-- Fully concrete two-side root-query preparation. -/
def prepareSides {k₀ k₁ : ℕ} (graphs₀ : Fin k₀ → FiniteRootedPlanar)
    (graphs₁ : Fin k₁ → FiniteRootedPlanar) (g : MixedCode) : Bool × List MixedCode :=
  (rootSide g, if rootSide g then (RootedRestriction.prepare graphs₁ (0,eraseDomains g)).2
    else (RootedRestriction.prepare graphs₀ (0,eraseDomains g)).2)

theorem fp_prepareSides {k₀ k₁ : ℕ} (graphs₀ : Fin k₀ → FiniteRootedPlanar)
    (graphs₁ : Fin k₁ → FiniteRootedPlanar) :
    FP MixedCode.encoding (BitEncoding.bool.prod MixedCode.encoding.list) (prepareSides graphs₀ graphs₁) := by
  have hroot := (fp_const MixedCode.encoding BitEncoding.nat 0).pair fp_eraseDomains
  have hp₀ := (hroot.comp (RootedRestriction.fp_prepare graphs₀)).comp
    (fp_snd BitEncoding.nat MixedCode.encoding.list)
  have hp₁ := (hroot.comp (RootedRestriction.fp_prepare graphs₁)).comp
    (fp_snd BitEncoding.nat MixedCode.encoding.list)
  exact (fp_rootSide.pair (fp_rootSide.ite hp₁ hp₀)).congr
    (fun g => by simp only [Function.comp_apply, prepareSides, rootSide, decide_eq_true_eq])

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

def recoverSides {k₀ k₁ : ℕ} (c₀ : Fin k₀ → K) (c₁ : Fin k₁ → K)
    (p : Bool × List K) : K :=
  if p.1 then RootedRestriction.recover c₁ (0,p.2) else RootedRestriction.recover c₀ (0,p.2)

theorem fp_recoverSides (basis : Module.Basis (Fin dimension) ℚ K)
    {k₀ k₁ : ℕ} (c₀ : Fin k₀ → K) (c₁ : Fin k₁ → K) :
    FP (BitEncoding.bool.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) (recoverSides c₀ c₁) := by
  have ha := (fp_const (BitEncoding.bool.prod (numberFieldEncoding basis).list) BitEncoding.nat 0).pair
    (fp_snd BitEncoding.bool (numberFieldEncoding basis).list)
  have ht := (fp_fst BitEncoding.bool (numberFieldEncoding basis).list).comp
    (fp_bool_unary BitEncoding.bool (fun b => decide (b = true)))
  exact ht.ite
    (ha.comp (RootedRestriction.fp_recover basis c₁))
    (ha.comp (RootedRestriction.fp_recover basis c₀))

end PlanarHom.HomogeneousSourceOrientation
