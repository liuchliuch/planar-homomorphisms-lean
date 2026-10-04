import PlanarHom.RepresentedAnswerConversion
import PlanarHom.GeneralFixedSubfieldDescent

/-! Changes of prescribed answer field are actual represented reductions.
Oracle replies are lifted by the concrete embedding converter; final answers
are descended by the general membership-promised subfield converter. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealPresentationReductions
open DensePolynomial Complexity FixedRealExtension RepresentedBit
variable {d e c f:ℕ} {K F D:Type} [Field K] [Field F]
variable [Algebra (RationalFunction d) K] [Algebra (RationalFunction c) F]

def embeddingReduction (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (small:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K)
    (ed:BitEncoding D) (nd:BitEncoding.Normalizer ed) (H:D→Prop) (v:D→F) :
    Reduction ((presentation ambient).problem ed H (fun a=>embed (v a)))
      ((presentation small).problem ed H v) :=
  answerConversionReduction (presentation small) (presentation ambient) ed nd H v (fun a=>embed (v a))
    (FixedPresentationConversion.run ambient small embed) (FixedPresentationConversion.fp_run ambient small embed)
    (fun a _ x _ hx=>⟨FixedPresentationConversion.run_valid ambient small embed x,
      (FixedPresentationConversion.run_value ambient small embed x).trans (congrArg embed hx)⟩)

def descent (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (small:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K) : Code d e→Code c f :=
  Classical.choose (GeneralFixedSubfieldDescent.exists_conversion ambient small embed)

theorem fp_descent (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (small:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K) :
    FP (encoding d e) (encoding c f) (descent ambient small embed) :=
  (Classical.choose_spec (GeneralFixedSubfieldDescent.exists_conversion ambient small embed)).1

theorem descent_correct (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (small:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K)
    (a:Code d e) (ha:Valid d a) (z:F) (hz:value ambient a=embed z) :
    Valid c (descent ambient small embed a) ∧ value small (descent ambient small embed a)=z :=
  (Classical.choose_spec (GeneralFixedSubfieldDescent.exists_conversion ambient small embed)).2 a ha z hz

def descentReduction (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (small:Module.Basis (Fin f) (RationalFunction c) F) (embed:F→+*K)
    (ed:BitEncoding D) (nd:BitEncoding.Normalizer ed) (H:D→Prop) (v:D→F) :
    Reduction ((presentation small).problem ed H v)
      ((presentation ambient).problem ed H (fun a=>embed (v a))) :=
  answerConversionReduction (presentation ambient) (presentation small) ed nd H (fun a=>embed (v a)) v
    (descent ambient small embed) (fp_descent ambient small embed)
    (fun a _ x hx hv=>descent_correct ambient small embed x hx (v a) hv)

/-- A common-field reduction is transported to the separately prescribed source
and target fields, charging all reply lifting and final descent. -/
def prescribedReduction {s r:ℕ} {S Q:Type} [Field S] [Algebra (RationalFunction s) S]
    (ambient:Module.Basis (Fin e) (RationalFunction d) K)
    (targetBasis:Module.Basis (Fin f) (RationalFunction c) F) (targetEmbed:F→+*K)
    (sourceBasis:Module.Basis (Fin r) (RationalFunction s) S) (sourceEmbed:S→+*K)
    (ed:BitEncoding D) (eq:BitEncoding Q) (nd:BitEncoding.Normalizer ed) (nq:BitEncoding.Normalizer eq)
    (HD:D→Prop) (HQ:Q→Prop) (v:D→F) (w:Q→S)
    (common:Reduction ((presentation ambient).problem ed HD (fun a=>targetEmbed (v a)))
      ((presentation ambient).problem eq HQ (fun a=>sourceEmbed (w a)))) :
    Reduction ((presentation targetBasis).problem ed HD v) ((presentation sourceBasis).problem eq HQ w) :=
  (descentReduction ambient targetBasis targetEmbed ed nd HD v).trans
    (common.trans (embeddingReduction ambient sourceBasis sourceEmbed eq nq HQ w))

end PlanarHom.FixedRealPresentationReductions
