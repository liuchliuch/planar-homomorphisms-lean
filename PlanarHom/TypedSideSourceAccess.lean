import PlanarHom.TypedBipartiteContext
import PlanarHom.ContextualGadgetClosure
import PlanarHom.FreshDomainOccurrenceMachines
import PlanarHom.HeterogeneousGraphReduction
import PlanarHom.SubtypeColorEvaluation
import PlanarHom.MixedColorProblemEquivalence

/-! Actual access to a same-side matrix from a retained typed language. Every
original vertex, including isolates, receives exactly the intrinsic X tag. The
ordinary unary alphabet is empty on the target, and the source's reserved tag
starts at its actual ordinary unary offset. No pinning oracle is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.TypedSideSourceAccess
open Complexity Complexity.MixedCode PrescribedDomains
open FiniteLabelLookupMachines PairProjectionMachines
open AlgebraicProductInterpolation AlgebraicProductInterpolation.RealLanguage
open TypedBipartiteContext TypedBipartiteSpectral
variable {x y n bt ut : ℕ}

theorem unaries_nil (g : MixedCode) (hg : g.Valid n 0) : g.unaries=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro u hu
  exact Nat.not_lt_zero _ (hg.2 u hu).2

/-- A source query on the original ambient color set. -/
def prepare (index : Fin n→Fin bt) (ut : ℕ) (g : MixedCode) : MixedCode :=
  (g.relabelBinary (finTable index)).withFreshDomains 0 ut

theorem fp_prepare (index : Fin n→Fin bt) (ut : ℕ) :
    FP encoding encoding (prepare index ut) :=
  ((fp_const encoding BitEncoding.unaryNat 0).pair (fp_relabelBinary (finTable index))).comp
    (fp_withFreshDomains ut)

theorem prepare_eq_withDomains (index : Fin n→Fin bt) (ut : ℕ) (g : MixedCode) :
    prepare index ut g = withDomains (unaryTypes:=ut)
      (g.relabelBinary (finTable index)) (fun _=>(0:Fin 2)) := by
  unfold prepare withFreshDomains withDomains domainOccurrences
  congr 2
  simp only [Nat.sub_zero,Nat.zero_add,Fin.val_zero,Nat.add_zero]
  rw [List.ofFn_eq_map,←List.map_coe_finRange]
  simp only [List.map_map,Function.comp_def]

theorem relabeled_valid (index : Fin n→Fin bt) (g : MixedCode) (hg : g.Valid n 0) :
    (g.relabelBinary (finTable index)).Valid bt ut := by
  have h := relabelBinary_valid (finTable index) hg (lookup_finTable_lt index)
  exact ⟨h.1,by simp [relabelBinary,unaries_nil g hg]⟩

theorem prepare_typed (index : Fin n→Fin bt)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hXX : ∀l,B (index l) 0 0) (g : MixedCode) (hg : g.PlanarValid n 0) :
    EncodedGraph B T (prepare index ut g) := by
  rw [prepare_eq_withDomains]
  apply encodedInput_encode_withDomains (hg:=relabeled_valid index g hg.1)
  · constructor
    · intro e he
      change e∈g.edges.map (fun e=>(e.1,e.2.1,lookup (finTable index) e.2.2)) at he
      obtain ⟨old,hold,rfl⟩ := List.mem_map.mp he
      have hv := hg.1.1 old hold
      change B ⟨lookup (finTable index) old.2.2,_⟩ 0 0
      have hi : (⟨lookup (finTable index) old.2.2, lookup_finTable_lt index _ hv.2.2⟩ : Fin bt)=index ⟨old.2.2,hv.2.2⟩ :=
        Fin.ext (lookup_finTable index ⟨old.2.2,hv.2.2⟩)
      rw [hi]
      exact hXX _
    · intro u hu
      have : u∈g.unaries := hu
      simp [unaries_nil g hg.1] at this
  · simpa only [relabelBinary_underlying] using hg.2

/-- The finite left color chart does not equate the ambient and X cardinalities. -/
def xColorEquiv (x y : ℕ) : Fin x≃(domains x y 0) :=
  Equiv.ofInjective (Fin.castAdd y) (Fin.castAdd_injective x y)

@[simp] theorem xColorEquiv_val (i : Fin x) : (xColorEquiv x y i).val=Fin.castAdd y i := rfl

variable {R : Type} [CommSemiring R]

theorem evaluate_const_domains (g : MixedCode) (hg : g.Valid bt 0)
    (M : Fin bt→Matrix (Fin (x+y)) (Fin (x+y)) R)
    (U : Fin ut→Fin (x+y)→R) :
    (withDomains (unaryTypes:=ut) g (fun _=>(0:Fin 2))).evaluate
      (withDomains_valid g (show g.Valid bt ut from ⟨hg.1,by simp [unaries_nil g hg]⟩) _)
      M (extendedUnaries U (domains x y)) (fun _=>1) =
    g.evaluate hg (fun l i j=>M l (Fin.castAdd y i) (Fin.castAdd y j))
      (fun l:Fin 0=>l.elim0) (fun _=>1) := by
  let hv : g.Valid bt ut := ⟨hg.1,by simp [unaries_nil g hg]⟩
  rw [evaluate_withDomains g hv]
  have hind : evaluateRestricted g hv M U (fun _=>1) (domains x y) (fun _=>(0:Fin 2))=
      g.evaluate hg M (fun l:Fin 0=>l.elim0) (indicator (domains x y 0)) := by
    unfold evaluateRestricted evaluate
    apply Finset.sum_congr rfl
    intro σ _
    simp only [unaries_nil g hg,List.map_nil,List.prod_nil,mul_one,Finset.prod_const_one,one_mul]
    have hi := indicator_product (R:=R) (domains x y) (fun _:Fin g.vertices=>(0:Fin 2)) σ
    rw [hi]
    split <;> simp_all
  rw [hind,evaluate_subset_colors g hg M (domains x y 0)]
  have he := (evaluate_color_equiv (xColorEquiv x y) g hg
    (fun l (i j : domains x y 0)=>M l i.val j.val) (fun l:Fin 0=>l.elim0) (fun _=>1)).symm
  have hu : (fun (l : Fin 0) (i : Fin x)=>(l.elim0 : domains x y 0→R) (xColorEquiv x y i))=
      (fun l:Fin 0=>l.elim0) := by funext l; exact l.elim0
  simpa only [xColorEquiv_val,hu] using he

variable {K : Type} [Field K] [Algebra ℚ K] {dimension : ℕ}

/-- The actual raw polynomial compiler for a finite family of selected X blocks.
Only the permission B(index l, X, X) is needed; all other source policies remain. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt→Matrix (Fin (x+y)) (Fin (x+y)) K)
    (U : Fin ut→Fin (x+y)→K) (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (index : Fin n→Fin bt) (hXX : ∀l,B (index l) 0 0) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun l i j=>M (index l) (Fin.castAdd y i) (Fin.castAdd y j))
        (fun l:Fin 0=>l.elim0) (fun _=>1))
      (domainEvaluationProblem basis M U (fun _=>1) (domains x y) B T) := by
  let MS := M
  let US := extendedUnaries U (domains x y)
  let r := reductionOfHeterogeneousPipeline basis BitEncoding.bits
    (fun l i j=>M (index l) (Fin.castAdd y i) (Fin.castAdd y j))
    (fun l:Fin 0=>l.elim0) (fun _=>1) MS US (fun _=>1)
    (PlanarValid n 0) (EncodedGraph B T) (fun _ h=>h.1) (fun _ h=>(h.planarValid B T).1)
    (fun g=>([],[prepare index ut g])) (fun z : Bits×List K=>z.2.sum)
    ((fp_const encoding BitEncoding.bits []).pair
      (((fp_prepare index ut).pair (fp_const encoding encoding.list [])).comp
        (ListMutationMachines.fp_cons encoding)))
    ((fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp (MaterializedFieldListMachines.fp_sum basis))
    (by
      intro g hg query hq
      obtain rfl := List.mem_singleton.mp hq
      exact prepare_typed index B T hXX g hg)
    (by
      intro g hg
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid MS US (fun _=>1) _ ((prepare_typed index B T hXX g hg).planarValid B T).1]
      simp only [prepare_eq_withDomains]
      have hr := relabelBinary_valid (finTable index) hg.1 (lookup_finTable_lt index)
      rw [evaluate_const_domains _ hr M U]
      exact evaluate_relabelBinary g hg.1 index
        (fun l i j=>M l (Fin.castAdd y i) (Fin.castAdd y j)) (fun l:Fin 0=>l.elim0) (fun _=>1))
  exact r.transport _ _ (fun _ h=>h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h) (fun _ _=>rfl) (fun _ _=>rfl)

/-- Canonical real-language access uses the real source field and its exact basis.
The selected source entries need agree with N only on X×X. -/
def canonicalReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (index : Fin n→Fin bt) (hXX : ∀l,B (index l) 0 0)
    (N : Fin n→Matrix (Fin x) (Fin x) ℝ) (hN : ∀l i j,IsAlgebraic ℚ (N l i j))
    (hblock : ∀l i j,L.matrices (index l) (Fin.castAdd y i) (Fin.castAdd y j)=N l i j) :
    PromisePolyTimeTuringReduction (unitLanguage N hN).problem
      (L.typedProblem (domains x y) B T) := by
  let NK := fun l i j=>L.matricesK (index l) (Fin.castAdd y i) (Fin.castAdd y j)
  have present := (unitLanguage N hN).presentationDescentReduction L.field L.basis
    NK (fun l:Fin 0=>l.elim0) (fun _=>1) hblock (fun l=>l.elim0) (fun _=>rfl)
  have hw : L.weightsK=(fun _=>1) := by funext i; exact Subtype.ext (hunit i)
  have r := reduction L.basis L.matricesK L.unariesK B T index hXX
  change PromisePolyTimeTuringReduction _
    (domainEvaluationProblem L.basis L.matricesK L.unariesK L.weightsK (domains x y) B T)
  rw [hw]
  exact present.trans r

/-- Singleton specialization of the constructed finite-family compiler. -/
def canonicalSingleReduction (L : RealLanguage (x+y) bt ut)
    (B : Fin bt→Fin 2→Fin 2→Prop) (T : Fin ut→Fin 2→Prop)
    (hunit : ∀i,L.weights i=1) (selected : Fin bt) (hXX : B selected 0 0)
    (N : Matrix (Fin x) (Fin x) ℝ) (hN : ∀i j,IsAlgebraic ℚ (N i j))
    (hblock : ∀i j,L.matrices selected (Fin.castAdd y i) (Fin.castAdd y j)=N i j) :
    PromisePolyTimeTuringReduction (unitLanguage (fun _:Fin 1=>N) (fun _=>hN)).problem
      (L.typedProblem (domains x y) B T) :=
  canonicalReduction L B T hunit (fun _=>selected) (fun _=>hXX)
    (fun _=>N) (fun _=>hN) (fun _=>hblock)

end PlanarHom.TypedSideSourceAccess
