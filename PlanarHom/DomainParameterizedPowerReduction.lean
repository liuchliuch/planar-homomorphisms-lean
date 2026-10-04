import PlanarHom.ParameterizedPowerReduction
import PlanarHom.RestrictedParameterizedGraphReduction
import PlanarHom.PrescribedDomainStretch

/-! Uniform powers with intrinsic prescribed-domain records. The selected
parameterized label has an explicit path-typing policy. Every private vertex
receives one already permitted full-domain record. Arbitrary endpoint policies
are never silently assumed to be closed under path replacement. -/
noncomputable section
namespace PlanarHom.DomainParameterizedPowerReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PrescribedDomains PairProjectionMachines
open ParameterizedPowerReduction
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u d : ℕ}

def sourceProblem (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) : PromiseProblem :=
  RestrictedMatrixFamilyReduction.targetProblem basis ex M (extendedUnaries U D) (fun _=>1)
    F allowed (EncodedGraph (appendOne B P) T)

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) : PromiseProblem :=
  sourceProblem basis (parameterEncoding ex) M U D B T P (family F) (fun p=>allowed p.2)

theorem target_valid_iff (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (raw : Bits) :
    (targetProblem basis ex M U D B T P F allowed).valid raw ↔
      ∃ p : ℕ×X, ∃ rawGraph : Bits,
        raw=BitEncoding.frame ((parameterEncoding ex).encode p)++rawGraph ∧
        allowed p.2 ∧ EncodedInput (appendOne B P) T rawGraph := by
  constructor
  · rintro ⟨⟨p,g⟩,hword,hp,hg⟩
    exact ⟨p,g.val,hword.symm,hp,(encodedInput_iff_graph _ T _).mpr
      ⟨g.value,g.decode_raw,hg⟩⟩
  · rintro ⟨p,rawGraph,hword,hp,hg⟩
    obtain ⟨g,hd,hg⟩:=(encodedInput_iff_graph _ T _).mp hg
    let gw : BitEncoding.ValidWord encoding:=⟨rawGraph,⟨g,hd⟩⟩
    refine ⟨(p,gw),hword.symm,hp,?_⟩
    have he : gw.value=g:=BitEncoding.ValidWord.value_eq (w:=gw) hd
    change EncodedGraph (appendOne B P) T gw.value
    rw [he]
    exact hg

/-- The same original endpoint permission is used for the power label. All
four possible path endpoint cases are required from the actual source policy. -/
theorem query_typed (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (full : Fin d)
    (hpath : ∀x y,P x y→PathDomainTyping (appendOne B P) (Fin.last b) full x y)
    (g : MixedCode) (hg : EncodedGraph (appendOne B P) T g) (k : ℕ) :
    EncodedGraph (appendOne B P) T (g.stretchLabelDomains b b (u+full.val) k) := by
  apply hg.stretchLabelDomains (Fin.last b) (Fin.last b) full (fun i _=>i.isLt)
  · intro i hi x y h
    exact h
  · simpa only [appendOne_aux] using hpath

def prepare (b u : ℕ) (full : Fin d) (p : (ℕ×X)×MixedCode) : Bits×List (X×MixedCode) :=
  ([],[(p.1.2,p.2.stretchLabelDomains b b (u+full.val) p.1.1)])

theorem fp_prepare (ex : BitEncoding X) (b u : ℕ) (full : Fin d) :
    FP ((parameterEncoding ex).prod encoding)
      (BitEncoding.bits.prod (ex.prod encoding).list) (prepare b u full) := by
  let ep:=parameterEncoding ex
  let input:=ep.prod encoding
  have hp:=fp_fst ep encoding
  have hk:=hp.comp (fp_fst BitEncoding.unaryNat ex)
  have hx:=hp.comp (fp_snd BitEncoding.unaryNat ex)
  have hg:=fp_snd ep encoding
  have query:=hx.pair ((hk.pair hg).comp (fp_stretchLabelDomains b b (u+full.val)))
  have singleton:=(query.pair (fp_const input (ex.prod encoding).list [])).comp
    (ListMutationMachines.fp_cons (ex.prod encoding))
  exact (fp_const input BitEncoding.bits []).pair singleton

theorem evaluate_query (g : MixedCode) (hg : g.Valid (b+1) (u+d)) (k : ℕ)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (A : Matrix (Fin q) (Fin q) K)
    (U : Fin u→Fin q→K) (D : Fin d→Set (Fin q)) (full : Fin d) (hfull : D full=Set.univ) :
    (g.stretchLabelDomains b b (u+full.val) k).evaluate
      (g.stretchLabelDomains_valid hg b b (u+full.val) k (Nat.lt_succ_self b)
        (Nat.add_lt_add_left full.isLt u) (fun e he _=>(hg.1 e he).2.2))
      (appendOne M A) (extendedUnaries U D) (fun _=>1)=
      g.evaluate hg (appendOne M (A^(k+1))) (extendedUnaries U D) (fun _=>1) := by
  have hf:=(g.stretchLabel b b k).evaluate_withFreshDomains
    (query_valid g hg k) g.vertices (Fin.natAdd u full) (appendOne M A)
    (extendedUnaries U D) (fun _=>1) (extendedUnaries_full U D full hfull)
  exact hf.trans (ParameterizedPowerReduction.evaluate_query g hg k M A (extendedUnaries U D))

def reduction_of_pathTyping (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (full : Fin d) (hfull : D full=Set.univ)
    (hpath : ∀x y,P x y→PathDomainTyping (appendOne B P) (Fin.last b) full x y)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (sourceProblem basis ex M U D B T P F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U D B T P F allowed)
      (sourceProblem basis ex M U D B T P F allowed) := by
  apply RestrictedParameterizedGraphReduction.reductionOfPipeline basis (parameterEncoding ex) ex BitEncoding.bits
    M (extendedUnaries U D) (fun _=>1) M (extendedUnaries U D) (fun _=>1)
    (family F) F (fun p=>allowed p.2) allowed
    (EncodedGraph (appendOne B P) T) (EncodedGraph (appendOne B P) T)
    (prepare b u full) recover (fp_prepare ex b u full) (fp_recover basis) ?_ ?_ base available
  · intro p ha hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    exact ⟨ha,query_typed B T P full hpath p.2 hg p.1.1⟩
  · intro p ha hg
    have ht:=(hg.planarValid _ T).1
    have hs:=((query_typed B T P full hpath p.2 hg p.1.1).planarValid _ T).1
    simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ ht,
      totalEvaluation_valid _ _ _ _ hs,family]
    exact evaluate_query p.2 ht p.1.1 M (F p.1.2) U D full hfull

def available_of_pathTyping (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (P : Fin d→Fin d→Prop) (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (full : Fin d) (hfull : D full=Set.univ)
    (hpath : ∀x y,P x y→PathDomainTyping (appendOne B P) (Fin.last b) full x y)
    (base : PromiseProblem) (source : PromisePolyTimeTuringReduction
      (sourceProblem basis ex M U D B T P F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U D B T P F allowed) base :=
  (reduction_of_pathTyping basis ex M U D B T P F allowed full hfull hpath base source).trans source

/-- A matrix globally available between existing domains satisfies all path
cases. The original companion permissions and vertex domains are retained. -/
def reduction_global (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (full : Fin d) (hfull : D full=Set.univ)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (sourceProblem basis ex M U D B T (fun _ _=>True) F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U D B T (fun _ _=>True) F allowed)
      (sourceProblem basis ex M U D B T (fun _ _=>True) F allowed) :=
  reduction_of_pathTyping basis ex M U D B T (fun _ _=>True) F allowed full hfull
    (by intro x y _; simp [PathDomainTyping,appendOne_aux]) base available

def available_global (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (full : Fin d) (hfull : D full=Set.univ)
    (base : PromiseProblem) (source : PromisePolyTimeTuringReduction
      (sourceProblem basis ex M U D B T (fun _ _=>True) F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U D B T (fun _ _=>True) F allowed) base :=
  (reduction_global basis ex M U D B T F allowed full hfull base source).trans source

end PlanarHom.DomainParameterizedPowerReduction
