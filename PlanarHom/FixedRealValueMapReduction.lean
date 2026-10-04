import PlanarHom.FixedRealMixedAliases
import PlanarHom.FixedRealLinearMapMachines
import PlanarHom.FixedRealTraceMachines
import PlanarHom.MixedEvaluationFieldMap

/-! NEW exact answer-presentation transport for the finite spectral extension.
Every fixed linear map is compiled from its dense coefficient table; oracle
answers may use any valid representative. Relative trace returns source-field
answers rather than silently changing the prescribed source presentation. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealValueMapReduction
open DensePolynomial Complexity RepresentedBit PairProjectionMachines FixedRealExtension
variable {n e f:ℕ} {E F:Type} [Field E] [Field F]
  [Algebra (RationalFunction n) E] [Algebra (RationalFunction n) F]

def reduction (input:Module.Basis (Fin e) (RationalFunction n) E)
    (output:Module.Basis (Fin f) (RationalFunction n) F) (L:E→ₗ[RationalFunction n] F)
    {A:Type} (ea:BitEncoding A) (na:BitEncoding.Normalizer ea) (H:A→Prop)
    (source:A→E) (target:A→F) (h:∀a,H a→L (source a)=target a) :
    Reduction ((presentation output).problem ea H target) ((presentation input).problem ea H source) := by
  let T:=FixedRealLinearMap.table input output L
  let prepare:A→ℕ×List A:=fun a=>(0,[a])
  let recover:ℕ×List (Code n e)→Code n f:=fun p=>
    FixedRealLinearMap.run T (p.2.headD (zeroCode n e))
  have hp:FP ea (BitEncoding.nat.prod ea.list) prepare:=
    (fp_const ea BitEncoding.nat 0).pair
      (((fp_id ea).pair (fp_const ea ea.list [])).comp (ListMutationMachines.fp_cons ea))
  have hr:FP (BitEncoding.nat.prod (encoding n e).list) (encoding n f) recover:=
    ((fp_snd _ _).comp (ListDecompositionMachines.fp_headD (encoding n e) (zeroCode n e))).comp
      (FixedRealLinearMap.fp_run T)
  apply presentationPipeline (presentation input) (presentation output) ea BitEncoding.nat ea
    na BitEncoding.natNormalizer H H target source prepare recover hp hr
  · intro a ha q hq
    exact (List.mem_singleton.mp hq) ▸ ha
  · intro a ha bs hbs
    change List.Forall₂ _ [a] bs at hbs
    cases hbs with
    | cons hb hrest=>
      cases hrest
      refine ⟨FixedRealLinearMap.run_valid T _ hb.1,?_⟩
      change value output (FixedRealLinearMap.run T _)=target a
      rw [FixedRealLinearMap.value_run T input output L (FixedRealLinearMap.table_realizes input output L)]
      exact (congrArg L hb.2).trans (h a ha)

variable {q bt ut:ℕ}
open FixedRealMixedInterpolation Complexity.MixedCode

def fieldMap (bF:Module.Basis (Fin f) (RationalFunction n) F)
    (bE:Module.Basis (Fin e) (RationalFunction n) E) (φ:F→ₐ[RationalFunction n] E)
    (M:Fin bt→Matrix (Fin q) (Fin q) F) (U:Fin ut→Fin q→F) (w:Fin q→F) :
    Reduction (problem bE (fun l i j=>φ (M l i j)) (fun l i=>φ (U l i)) (fun i=>φ (w i)))
      (problem bF M U w) := by
  apply reduction bF bE φ.toLinearMap MixedCode.encoding MixedCode.normalizer (PlanarValid bt ut)
    (totalEvaluation M U w) (totalEvaluation (fun l i j=>φ (M l i j)) (fun l i=>φ (U l i)) (fun i=>φ (w i)))
  intro g hg
  simp only [totalEvaluation_valid _ _ _ g hg.1]
  exact map_evaluate φ.toRingHom g hg.1 M U w

variable [CharZero F] [Algebra F E] [IsScalarTower (RationalFunction n) F E] [FiniteDimensional F E]

def fieldDescent (bF:Module.Basis (Fin f) (RationalFunction n) F)
    (bE:Module.Basis (Fin e) (RationalFunction n) E)
    (M:Fin bt→Matrix (Fin q) (Fin q) F) (U:Fin ut→Fin q→F) (w:Fin q→F) :
    Reduction (problem bF M U w)
      (problem bE (fun l i j=>algebraMap F E (M l i j))
        (fun l i=>algebraMap F E (U l i)) (fun i=>algebraMap F E (w i))) := by
  apply reduction bE bF (FixedRealTrace.traceMap (d:=n)) MixedCode.encoding MixedCode.normalizer
    (PlanarValid bt ut)
    (totalEvaluation (fun l i j=>algebraMap F E (M l i j))
      (fun l i=>algebraMap F E (U l i)) (fun i=>algebraMap F E (w i))) (totalEvaluation M U w)
  intro g hg
  simp only [totalEvaluation_valid _ _ _ g hg.1]
  rw [←map_evaluate (algebraMap F E) g hg.1 M U w]
  exact Algebra.normalizedTrace_algebraMap_apply_eq_self F E _

end PlanarHom.FixedRealValueMapReduction
