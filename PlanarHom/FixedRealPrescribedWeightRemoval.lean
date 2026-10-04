import PlanarHom.FixedRealWeightPowerExtension
import PlanarHom.GeneralFixedSubfieldDescent

/-! NEW complete prescribed-output-field A.8 endpoint. Source weights may add
transcendental constants absent from the target field. The actual A.1 general
subfield converter constructs the descent, with no conversion assumption. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealWeightRemoval
open DensePolynomial Complexity Complexity.MixedCode RepresentedBit FixedRealExtension
open FixedRealMixedInterpolation PairProjectionMachines RelativeWeightedSpectralField
variable {n e c f q bt ut:ℕ} {K F:Type} [Field K] [Field F]
  [Algebra (RationalFunction n) K] [Algebra (RationalFunction c) F]

/-- One unchanged graph query followed by the actual prescribed-subfield
converter; every valid oracle representative is accepted. -/
def prescribedDescent (sourceBasis:Module.Basis (Fin e) (RationalFunction n) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K)
    (M:Fin bt→Matrix (Fin q) (Fin q) F) (U:Fin ut→Fin q→F) :
    Reduction (problem targetBasis M U (fun _=>1))
      (problem sourceBasis (fun l i j=>embed (M l i j)) (fun l i=>embed (U l i)) (fun _=>1)) := by
  let hex:=GeneralFixedSubfieldDescent.exists_conversion sourceBasis targetBasis embed
  let convert:=Classical.choose hex
  have hfp:=(Classical.choose_spec hex).1
  have hconvert:=(Classical.choose_spec hex).2
  let prepare:MixedCode→ℕ×List MixedCode:=fun g=>(0,[g])
  let recover:ℕ×List (Code n e)→Code c f:=fun p=>convert (p.2.headD (zeroCode n e))
  have hp:FP MixedCode.encoding (BitEncoding.nat.prod MixedCode.encoding.list) prepare:=
    (fp_const MixedCode.encoding BitEncoding.nat 0).pair
      (((fp_id MixedCode.encoding).pair (fp_const MixedCode.encoding MixedCode.encoding.list [])).comp
        (ListMutationMachines.fp_cons MixedCode.encoding))
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding c f) recover:=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD (encoding n e) (zeroCode n e))).comp hfp
  apply presentationPipeline (presentation sourceBasis) (presentation targetBasis)
    MixedCode.encoding BitEncoding.nat MixedCode.encoding MixedCode.normalizer BitEncoding.natNormalizer
    (PlanarValid bt ut) (PlanarValid bt ut) (totalEvaluation M U (fun _=>1))
    (totalEvaluation (fun l i j=>embed (M l i j)) (fun l i=>embed (U l i)) (fun _=>1))
    prepare recover hp hr
  · intro g hg h hh
    exact (List.mem_singleton.mp hh) ▸ hg
  · intro g hg bs hbs
    change List.Forall₂ _ [g] bs at hbs
    cases hbs with
    | cons hb hrest=>
      cases hrest
      apply hconvert _ hb.1 (totalEvaluation M U (fun _=>1) g)
      refine hb.2.trans ?_
      simp only [totalEvaluation_valid _ _ _ g hg.1]
      simpa only [map_one] using (map_evaluate embed g hg.1 M U (fun _=>1)).symm

variable [Algebra K ℝ]

/-- Theorem A.8, with arbitrary prescribed fixed-field representations on both
sides and no algebraicity-over-Q restriction on the positive background. -/
def theoremA8 (sourceBasis:Module.Basis (Fin e) (RationalFunction n) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K)
    (M:Fin bt→Matrix (Fin q) (Fin q) F) (U:Fin ut→Fin q→F) (w:Fin q→K) (old:Fin bt)
    (hs:∀i j,algebraMap K ℝ (embed (M old i j))=algebraMap K ℝ (embed (M old j i)))
    (hw:∀i,0<realWeights w i)
    (hnonzero:∀i,(fun j=>algebraMap K ℝ (embed (M old i j)))≠0)
    (hproj:∀i j,i≠j→∀t:ℝ,(fun k=>algebraMap K ℝ (embed (M old i k)))≠
      t • (fun k=>algebraMap K ℝ (embed (M old j k)))) :
    Reduction (problem targetBasis M U (fun _=>1))
      (problem sourceBasis (fun l i j=>embed (M l i j)) (fun l i=>embed (U l i)) w) :=
  (prescribedDescent sourceBasis targetBasis embed M U).trans
    (removePositiveWeights sourceBasis (fun l i j=>embed (M l i j)) (fun l i=>embed (U l i)) w old
      hs hw hnonzero hproj)

end PlanarHom.FixedRealWeightRemoval
