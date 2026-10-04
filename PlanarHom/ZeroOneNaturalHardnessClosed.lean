import PlanarHom.ZeroOneTheorem71Closed
import PlanarHom.ZeroOneGraphMixedLift
import PlanarHom.NonadaptiveReductionCompiler
import PlanarHom.FixedFieldPolynomialMachines

/-! NEW charged ordinary-MixedCode to natural GraphCode count reduction.
Queries erase only homogeneous zero labels; source promises are ordinary
planarity, and answer conversion is a compiled natural-to-field map. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.ZeroOneMixedMembership
open Complexity Complexity.MixedCode PairProjectionMachines MachineComposition
open AlgebraicProductInterpolation

private def rawView {q : ℕ} (L : RealLanguage q 1 0) (raw : Bits) (h : L.problem.valid raw) :
    BitEncoding.ValidWord MixedCode.encoding :=
  ⟨raw,by obtain ⟨g,hd,_⟩:=h;exact ⟨g,hd⟩⟩

private theorem rawView_property {q : ℕ} (L : RealLanguage q 1 0) (raw : Bits) (h : L.problem.valid raw) :
    (rawView L raw h).value.PlanarValid 1 0 := by
  obtain ⟨g,hd,hg⟩:=h
  have he:(rawView L raw ⟨g,hd,hg⟩).value=g:=BitEncoding.ValidWord.value_eq hd
  rw [he]
  exact hg

def toNaturalCount {q : ℕ} (L : RealLanguage q 1 0)
    (hunit : ∀i,L.weights i=1) (h01 : ∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    PromisePolyTimeTuringReduction L.problem (ZeroOneSharpPMembership.planarProblem q (realRelation L)) := by
  let prepare : MixedCode→Bits×List GraphCode:=fun g=>([],[g.underlying])
  let answer : GraphCode→ℕ:=fun g=>ZeroOneSharpPMembership.totalCount q (realRelation L) (GraphCode.encoding.encode g)
  let recover : Bits×List ℕ→L.field:=fun p=>(p.2.map (fun n : ℕ=>(n:L.field))).sum
  have hp : FP MixedCode.encoding (BitEncoding.bits.prod GraphCode.encoding.list) prepare :=
    (fp_const MixedCode.encoding BitEncoding.bits []).pair
      ((fp_underlying.pair (fp_const MixedCode.encoding GraphCode.encoding.list [])).comp
        (ListMutationMachines.fp_cons GraphCode.encoding))
  have hr : FP (BitEncoding.bits.prod BitEncoding.nat.list) (numberFieldEncoding L.basis) recover :=
    ((fp_snd BitEncoding.bits BitEncoding.nat.list).comp
      ((ListMapMachines.fp_map _ _ _ (FixedFieldPolynomialMachines.fp_natCast L.basis)).comp
        (MaterializedFieldListMachines.fp_sum L.basis))).congr (by intro p; simp [recover,Function.comp_def])
  let pre:=composeComputers MixedCode.normalizer (Classical.choice hp)
  apply nonadaptiveReduction (p:=ZeroOneSharpPMembership.outputPolynomial q)
    (BitEncoding.ValidWord.encoding MixedCode.encoding) BitEncoding.bits GraphCode.encoding
    BitEncoding.nat (numberFieldEncoding L.basis) L.problem
    (ZeroOneSharpPMembership.planarProblem q (realRelation L))
    (prepare ∘ BitEncoding.ValidWord.value) answer recover pre (Classical.choice hr) (rawView L) (fun _ _=>rfl)
  · intro raw h query hq
    have hg:=rawView_property L raw h
    have he:query=(rawView L raw h).value.underlying:=by simpa [prepare,Function.comp_def] using hq
    subst query
    exact ⟨_,GraphCode.encoding.decode_encode _,hg.2⟩
  · intro query _
    rfl
  · intro raw h
    have hg:=rawView_property L raw h
    change (numberFieldEncoding L.basis).encode
      ((([answer (rawView L raw h).value.underlying]).map (fun n : ℕ=>(n:L.field))).sum)=_
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    have hc:answer (rawView L raw h).value.underlying=
        ZeroOneSharpPMembership.count q (realRelation L) (rawView L raw h).value.underlying
          ((rawView L raw h).value.underlying_valid hg.1):=
      ZeroOneSharpPMembership.totalCount_decode q (realRelation L) _ _ (GraphCode.encoding.decode_encode _) _
    rw [hc,←evaluate_eq_count L hunit h01 _ hg.1]
    exact (evaluationValue_decode L.basis L.matricesK L.unariesK L.weightsK raw _
      (BitEncoding.ValidWord.decode_raw (rawView L raw h)) hg.1).symm
  · intro raw _
    exact ZeroOneSharpPMembership.totalCount_output_bound q (realRelation L) raw

end PlanarHom.ZeroOneMixedMembership
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity

theorem theorem71_natural_hard {q : ℕ} (L : RealLanguage q 1 0) (hunit : ∀i,L.weights i=1)
    (hs : ∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01 : ∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) (hbad : ¬L.BasicZeroOneSupport hs) :
    PromisedSharpPHard (ZeroOneSharpPMembership.planarProblem q (ZeroOneMixedMembership.realRelation L)) :=
  ((L.theorem71_unweighted hunit hs h01).2.1 hbad).trans
    (ZeroOneMixedMembership.toNaturalCount L hunit h01)

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
