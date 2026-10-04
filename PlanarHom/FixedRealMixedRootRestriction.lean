import PlanarHom.MixedRootedProjection
import PlanarHom.FixedRealComponentReduction
import PlanarHom.FixedRealRootRestriction
import PlanarHom.RepresentedFixedLinearListSemantics

/-! Full finite mixed-language single-root restriction over the honest fixed-
real extension presentation. Fixed projection constants are source data, while
query attachment and arbitrary-representative recovery are actual FP machines. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.FixedRealMixedRootRestriction
open DensePolynomial Complexity Complexity.MixedCode FixedRealExtension RepresentedBit
variable {n e b u:ℕ} {K C:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K)

def inputValid (p:ℕ×MixedCode) : Prop := p.2.PlanarValid b u ∧ p.1<p.2.vertices

def rootValue (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (X:Set C) (p:ℕ×MixedCode) : K :=
  if hg:p.2.Valid b u then
    if hr:p.1<p.2.vertices then (p.2.toMixedInstance hg).rootRestricted ⟨p.1,hr⟩ M U w X else 0
  else 0

def rootProblem (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K) (X:Set C) : Problem :=
  (presentation basis).problem RootedCodeMachines.inputEncoding (inputValid (b:=b) (u:=u)) (rootValue M U w X)

def prepare {s:ℕ} (graphs:Fin s→FiniteMixedRooted b u) (p:ℕ×MixedCode) : ℕ×List MixedCode :=
  (0,List.ofFn (fun j=>MixedRootedCodeMachines.attach (graphs j).2.2.2.val p))

theorem fp_prepare {s:ℕ} (graphs:Fin s→FiniteMixedRooted b u) :
    FP RootedCodeMachines.inputEncoding (BitEncoding.nat.prod MixedCode.encoding.list) (prepare graphs) := by
  have hv:=FixedVectorMachines.fp_assemble RootedCodeMachines.inputEncoding MixedCode.encoding s
    (fun p j=>MixedRootedCodeMachines.attach (graphs j).2.2.2.val p)
    (fun j=>MixedRootedCodeMachines.fp_attach _)
  have hl:FP RootedCodeMachines.inputEncoding MixedCode.encoding.list
      (fun p=>List.ofFn (fun j=>MixedRootedCodeMachines.attach (graphs j).2.2.2.val p)):=
    hv.transportOutput (fun _=>rfl)
  exact (fp_const _ _ 0).pair hl

variable [LinearOrder K] [IsStrictOrderedRing K]

/-- Corollary A.2's arbitrary root subset with a fixed retained mixed language.
This makes no all-vertex restriction assertion for an arbitrary subset. -/
def corollaryA2_mixed_root (M:Fin b→Matrix C C K) (U:Fin u→C→K) (w:C→K)
    (hw:∀i,0 < w i) (X:Set C) :
    Reduction (rootProblem basis M U w X) (FixedRealComponents.problem basis M U w) := by
  let data:=MixedRootedRestriction.exists_computed_queries M U w hw X
  let s:=Classical.choose data
  let graphs:=Classical.choose (Classical.choose_spec data)
  let c:=Classical.choose (Classical.choose_spec (Classical.choose_spec data))
  have hcorrect:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data))
  let P:=presentation basis
  let ops:=FixedRealRootRestriction.arithmetic basis
  let recover:ℕ×List (Code n e)→Code n e:=fun p=>ops.dot s (fun j=>P.constant (c j)) p.2
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n e) recover:=
    (PairProjectionMachines.fp_snd _ _).comp (ops.fp_dot _ _)
  apply presentationPipeline P P RootedCodeMachines.inputEncoding BitEncoding.nat MixedCode.encoding
    (BitEncoding.prodNormalizer BitEncoding.natNormalizer MixedCode.normalizer) BitEncoding.natNormalizer
    (inputValid (b:=b) (u:=u)) (PlanarValid b u) (rootValue M U w X) (totalEvaluation M U w)
    (prepare graphs) recover (fp_prepare graphs) hr
  · intro p hp query hq
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq
    exact MixedRootedCodeMachines.attach_planarValid _ (graphs j).2.2.2.property p.2 hp.1 ⟨p.1,hp.2⟩
  · intro p hp bs hbs
    have hb:=FixedRealComponents.represented_answers basis _ bs (totalEvaluation M U w) hbs
    have hy:bs.map P.value=List.ofFn (fun j=>totalEvaluation M U w
        (MixedRootedCodeMachines.attach (graphs j).2.2.2.val p)):=by
      simpa only [prepare,List.map_ofFn] using hb.2
    have hd:=ops.dot_list s c bs hb.1 _ hy
    refine ⟨hd.1,hd.2.trans ?_⟩
    simp only [rootValue,dif_pos hp.1.1,dif_pos hp.2]
    exact (hcorrect p.2 hp.1 ⟨p.1,hp.2⟩).symm

end PlanarHom.FixedRealMixedRootRestriction
