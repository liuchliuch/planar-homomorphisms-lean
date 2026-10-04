import PlanarHom.TypedSideSourceAccessFamily
import PlanarHom.HomogeneousSourceOrientationMachines
import PlanarHom.ListPredicateMachines

/-! NEW ordinary-source access for the full left side and an empty right side.
The actual input program reads the intrinsic domain tags. Right-side requests
have value zero; every other request becomes the same ordinary source graph.
This supplies a genuine source for the already proved typed closure machinery. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.SingleSideSourceReduction
open Complexity Complexity.MixedCode PrescribedDomains TypedBipartiteContext
open HomogeneousSourceOrientation PairProjectionMachines ArithmeticCircuitPrimitives
variable {q b dimension : ℕ}

def hasRight (g : MixedCode) : Bool := g.unaries.any (fun p => decide (p.2 = 1))

theorem fp_hasRight : FP encoding BitEncoding.bool hasRight := by
  have he := ((fp_snd BitEncoding.nat BitEncoding.nat).pair
    (fp_const (BitEncoding.nat.prod BitEncoding.nat) BitEncoding.nat 1)).comp
      NatListSumMachines.fp_equal
  exact MixedCode.fp_unaries.comp
    (ListPredicateMachines.fp_any (BitEncoding.nat.prod BitEncoding.nat) _ he)

theorem hasRight_withDomains_iff (g : MixedCode) (hg : g.Valid b 0)
    (δ : Fin g.vertices → Fin 2) :
    hasRight (withDomains (unaryTypes := 0) g δ) = true ↔ ∃ v, δ v = 1 := by
  simp only [hasRight,withDomains,TypedSideSourceAccess.unaries_nil g hg,
    List.nil_append,domainOccurrences]
  simp only [List.any_eq_true,List.mem_ofFn,decide_eq_true_eq]
  constructor
  · rintro ⟨p,⟨v,rfl⟩,h⟩
    exact ⟨v,Fin.ext (by simpa using h)⟩
  · rintro ⟨v,h⟩
    exact ⟨(v.val,(δ v).val),⟨v,by simp⟩,by simp [h]⟩

theorem mem_domains_iff (i : Fin q) (d : Fin 2) :
    i ∈ domains q 0 d ↔ d = 0 := by
  fin_cases d
  · exact ⟨fun _ => rfl, fun _ => ⟨i,rfl⟩⟩
  · change (∃ j : Fin 0, Fin.natAdd q j = i) ↔ (1 : Fin 2) = 0
    simp

theorem allowed_iff {V : Type} (δ : V → Fin 2) (σ : V → Fin q) :
    Allowed (domains q 0) δ σ ↔ ∀ v, δ v = 0 := by
  simp only [Allowed,mem_domains_iff]

theorem erase_eq (g : MixedCode) (hg : g.Valid b 0) (δ : Fin g.vertices → Fin 2) :
    eraseDomains (withDomains (unaryTypes := 0) g δ) = g := by
  cases g with
  | mk n es us =>
    have hu := TypedSideSourceAccess.unaries_nil ⟨n,es,us⟩ hg
    simp only [MixedCode.unaries] at hu
    subst us
    rfl

variable {K : Type} [Field K] [Algebra ℚ K]

theorem evaluateRestricted_eq (g : MixedCode) (hg : g.Valid b 0)
    (δ : Fin g.vertices → Fin 2) (M : Fin b → Matrix (Fin q) (Fin q) K)
    (U : Fin 0 → Fin q → K) (w : Fin q → K) :
    evaluateRestricted g hg M U w (domains q 0) δ =
      if hasRight (withDomains (unaryTypes := 0) g δ) then 0 else g.evaluate hg M U w := by
  by_cases hd : hasRight (withDomains (unaryTypes := 0) g δ) = true
  · obtain ⟨v,hv⟩ := (hasRight_withDomains_iff g hg δ).mp hd
    have hn : ¬∀ v, δ v = 0 := fun h => by have := (h v).symm.trans hv; exact Fin.zero_ne_one this
    simp [evaluateRestricted,allowed_iff,hn,hd]
  · have hzero : ∀ v, δ v = 0 := by
      intro v
      have hv : δ v ≠ 1 := fun h => hd ((hasRight_withDomains_iff g hg δ).mpr ⟨v,h⟩)
      apply Fin.ext
      have hlt := (δ v).isLt
      have hne : (δ v).val ≠ 1 := fun h => hv (Fin.ext h)
      change (δ v).val = 0
      omega
    simp [evaluateRestricted,allowed_iff,hzero,hd,evaluate]

def prepare (g : MixedCode) : Bool × List MixedCode := (hasRight g,[eraseDomains g])

def recover (p : Bool × List K) : K := if p.1 then 0 else p.2.sum

theorem fp_prepare : FP encoding (BitEncoding.bool.prod encoding.list) prepare := by
  exact fp_hasRight.pair ((fp_eraseDomains.pair
    (fp_const encoding encoding.list [])).comp (ListMutationMachines.fp_cons encoding))

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (BitEncoding.bool.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) (recover (K:=K)) := by
  have hb := (fp_fst BitEncoding.bool (numberFieldEncoding basis).list).comp
    (fp_bool_unary BitEncoding.bool (fun b => decide (b = true)))
  exact hb.ite (fp_const _ _ 0)
    ((fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis))

def reduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b → Matrix (Fin q) (Fin q) K) (U : Fin 0 → Fin q → K) (w : Fin q → K)
    (B : Fin b → Fin 2 → Fin 2 → Prop) (T : Fin 0 → Fin 2 → Prop) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w (domains q 0) B T)
      (evaluationProblem basis M U w) := by
  let r := reductionOfPipeline basis BitEncoding.bool
    M (extendedUnaries U (domains q 0)) w M U w
    (EncodedGraph B T) (PlanarValid b 0) (fun _ h => h.planarValid.1) (fun _ h => h.1)
    prepare recover fp_prepare (fp_recover basis) (by
      intro code hc query hq
      obtain ⟨g,hg,δ,ht,hp,he⟩ := hc
      rw [encoding.decode_encode] at he
      obtain rfl := Option.some.inj he
      have hquery : query = g := by
        have := List.mem_singleton.mp hq
        simpa only [prepare,erase_eq g hg] using this
      subst query
      exact ⟨hg,hp⟩) (by
      intro code hc
      obtain ⟨g,hg,δ,ht,hp,he⟩ := hc
      rw [encoding.decode_encode] at he
      obtain rfl := Option.some.inj he
      simp only [prepare,recover,erase_eq g hg,List.map_cons,List.map_nil,
        List.sum_cons,List.sum_nil,add_zero]
      rw [totalEvaluation_valid M U w g hg]
      rw [evaluate_withDomains g hg]
      exact (evaluateRestricted_eq g hg δ M U w).symm)
  exact r.transport _ _ (fun _ h => (encodedInput_iff_graph B T _).mp h)
    (fun _ h => h) (fun _ _ => rfl) (fun _ _ => rfl)

end PlanarHom.SingleSideSourceReduction
