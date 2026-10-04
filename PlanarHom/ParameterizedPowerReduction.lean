import PlanarHom.ParameterizedGraphReduction
import PlanarHom.SelectedStretchAppend
import PlanarHom.MaterializedFieldListMachines

/-! Uniform positive matrix powers of an available parameterized label. The
parameter is `(k,x)` with the exact `unaryNat.prod ex` codec; a selected last
label becomes a path of `k+1` copies of `F x`. All companion occurrences and
unaries survive, and private vertices have unit background weight. -/
noncomputable section
namespace PlanarHom.ParameterizedPowerReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases PairProjectionMachines
variable {X K : Type} [Field K] [Algebra ℚ K] {dimension q b u : ℕ}

def family (F : X→Matrix (Fin q) (Fin q) K) (p : ℕ×X) : Matrix (Fin q) (Fin q) K :=
  F p.2 ^ (p.1+1)

omit [Algebra ℚ K] in
@[simp] theorem family_zero (F : X→Matrix (Fin q) (Fin q) K) (x : X) :
    family F (0,x)=F x := by simp [family]

def parameterEncoding (ex : BitEncoding X) : BitEncoding (ℕ×X) :=
  BitEncoding.unaryNat.prod ex

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) : PromiseProblem :=
  ParameterizedMatrixEvaluation.problem basis (parameterEncoding ex) M U (fun _=>1)
    (family F) (fun p=>allowed p.2)

/-- The original raw planar promise is retained, with a canonical pair of
parameter words. In particular there is no embedding or loop-free promise. -/
theorem target_valid_iff (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop) (raw : Bits) :
    (targetProblem basis ex M U F allowed).valid raw ↔
      ∃ p : ℕ×X, ∃ rawGraph : Bits,
        raw=BitEncoding.frame ((parameterEncoding ex).encode p)++rawGraph ∧
        allowed p.2 ∧ PlanarInput (b+1) u rawGraph :=
  ParameterizedMatrixEvaluation.valid_iff_rawGraph basis (parameterEncoding ex)
    M U (fun _=>1) (family F) (fun p=>allowed p.2) raw

omit [Algebra ℚ K] in
theorem pathPowerLabels_eq (M : Fin b→Matrix (Fin q) (Fin q) K)
    (A : Matrix (Fin q) (Fin q) K) (k : ℕ) :
    pathPowerLabels (a:=b+1) (appendOne M A) b (Fin.last b) k =
      appendOne M (A^(k+1)) := by
  funext i
  refine Fin.lastCases ?_ (fun j=>?_) i
  · simp [pathPowerLabels,appendOne_aux]
  · change pathPowerLabels (appendOne M A) b (Fin.last b) k (Fin.castAdd 1 j)=
      appendOne M (A^(k+1)) (Fin.castAdd 1 j)
    simp only [pathPowerLabels,Fin.coe_castAdd,j.isLt.ne,if_false,
      dif_pos (j.isLt.trans (Nat.lt_succ_self b)),appendOne_old]
    change appendOne M A (Fin.castAdd 1 j)=M j
    exact appendOne_old M A j

theorem query_valid (g : MixedCode) (hg : g.Valid (b+1) u) (k : ℕ) :
    (g.stretchLabel b b k).Valid (b+1) u :=
  g.stretchLabel_valid hg b b k (Nat.lt_succ_self b) (fun e he _=>(hg.1 e he).2.2)

/-- Ordinary topological planarity, including selected loops and no selected
occurrences, follows from the actual selected-path incidence equivalence. -/
theorem query_planar (g : MixedCode) (hg : g.PlanarValid (b+1) u) (k : ℕ) :
    (g.stretchLabel b b k).PlanarValid (b+1) u :=
  g.stretchLabel_planar hg b b k (Nat.lt_succ_self b) (fun e he _=>(hg.1.1 e he).2.2)

/-- With no selected occurrences the emitted mixed code is literally unchanged,
at every unary path parameter, including zero. -/
theorem query_of_noSelected (g : MixedCode) (b k : ℕ)
    (h : ∀e∈g.edges,e.2.2≠b) : g.stretchLabel b b k=g := by
  have hs : g.selectedEdges b=[] := by
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro e he
    have hm:=List.mem_filter.mp he
    exact h e hm.1 (by simpa using hm.2)
  have hc : g.companionEdges b=g.edges := by
    apply List.filter_eq_self.mpr
    intro e he
    simpa using h e he
  change MixedCode.mk (g.stretchLabel b b k).vertices (g.stretchLabel b b k).edges
    (g.stretchLabel b b k).unaries = MixedCode.mk g.vertices g.edges g.unaries
  congr 1
  · simp only [stretchLabel_vertices,hs,List.length_nil,Nat.zero_mul,Nat.add_zero]
  · simp only [stretchLabel_edges_eq_flatMap,hs,List.zipIdx_nil,List.flatMap_nil,List.nil_append,hc]

omit [Algebra ℚ K] in
theorem evaluate_query (g : MixedCode) (hg : g.Valid (b+1) u) (k : ℕ)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (A : Matrix (Fin q) (Fin q) K)
    (U : Fin u→Fin q→K) :
    (g.stretchLabel b b k).evaluate (query_valid g hg k) (appendOne M A) U (fun _=>1)=
      g.evaluate hg (appendOne M (A^(k+1))) U (fun _=>1) := by
  simpa only [pathPowerLabels_eq] using
    g.evaluate_stretchLabel hg b k (Fin.last b) (fun e he _=>(hg.1 e he).2.2)
      (appendOne M A) U

def prepare (b : ℕ) (p : (ℕ×X)×MixedCode) : Bits×List (X×MixedCode) :=
  ([],[(p.1.2,p.2.stretchLabel b b p.1.1)])

theorem fp_prepare (ex : BitEncoding X) (b : ℕ) :
    FP ((parameterEncoding ex).prod encoding)
      (BitEncoding.bits.prod (ex.prod encoding).list) (prepare b) := by
  let ep:=parameterEncoding ex
  let input:=ep.prod encoding
  have hp:=fp_fst ep encoding
  have hk:=hp.comp (fp_fst BitEncoding.unaryNat ex)
  have hx:=hp.comp (fp_snd BitEncoding.unaryNat ex)
  have hg:=fp_snd ep encoding
  have query:=hx.pair ((hk.pair hg).comp (fp_stretchLabel b b))
  have singleton:=(query.pair (fp_const input (ex.prod encoding).list [])).comp
    (ListMutationMachines.fp_cons (ex.prod encoding))
  exact (fp_const input BitEncoding.bits []).pair singleton

def recover (p : Bits×List K) : K := p.2.sum

theorem fp_recover (basis : Module.Basis (Fin dimension) ℚ K) :
    FP (BitEncoding.bits.prod (numberFieldEncoding basis).list)
      (numberFieldEncoding basis) (recover (K:=K)) :=
  (fp_snd BitEncoding.bits (numberFieldEncoding basis).list).comp
    (MaterializedFieldListMachines.fp_sum basis)

/-- Actual unary-parameter power reduction. The supplied source availability
only charges oracle answer lengths; no evaluator for `F`, parameter normalizer,
or unproved polynomial-time graph transformation is assumed. -/
def reduction (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U (fun _=>1) F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U F allowed)
      (ParameterizedMatrixEvaluation.problem basis ex M U (fun _=>1) F allowed) := by
  apply ParameterizedGraphReduction.reductionOfPipeline basis (parameterEncoding ex) ex BitEncoding.bits
    M U (fun _=>1) M U (fun _=>1) (family F) F (fun p=>allowed p.2) allowed
    (prepare b) recover (fp_prepare ex b) (fp_recover basis) ?_ ?_ base available
  · intro p ha hg query hq
    obtain rfl:=List.mem_singleton.mp hq
    exact ⟨ha,query_planar _ hg _⟩
  · intro p ha hg
    have hv:=query_valid p.2 hg.1 p.1.1
    simp only [prepare,recover,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero,
      ParameterizedMatrixEvaluation.answer,totalEvaluation_valid _ _ _ _ hg.1,
      totalEvaluation_valid _ _ _ _ hv,family]
    exact evaluate_query _ hg.1 _ M (F p.1.2) U

def available (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (F : X→Matrix (Fin q) (Fin q) K) (allowed : X→Prop)
    (base : PromiseProblem) (source : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex M U (fun _=>1) F allowed) base) :
    PromisePolyTimeTuringReduction (targetProblem basis ex M U F allowed) base :=
  (reduction basis ex M U F allowed base source).trans source

end PlanarHom.ParameterizedPowerReduction
