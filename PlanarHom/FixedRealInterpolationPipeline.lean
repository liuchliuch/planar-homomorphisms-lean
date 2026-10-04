import PlanarHom.FixedRealInterpolationRecovery
import PlanarHom.RepresentedInterpolationNodeTransport
import PlanarHom.RepresentedPresentationPipeline

/-! Complete charged nonadaptive interpolation reduction over a fixed finite
extension of Q(X). Only the application's exact field identity and graph-query
promise preservation remain parameters; every arithmetic machine is concrete. -/
noncomputable section
open Classical
namespace PlanarHom.FixedRealInterpolationPipeline
open DensePolynomial Complexity RepresentedBit RepresentedPowerTable FixedRealExtension
open FixedRealInterpolationProducts RepresentedInterpolationMatrices PairProjectionMachines
variable {n e t:ℕ} {K:Type} [Field K] [Algebra (RationalFunction n) K]
variable (basis:Module.Basis (Fin e) (RationalFunction n) K) (A B:Fin t→K)

abbrev metadata := List (Row (presentation basis) t)
def metaEncoding : BitEncoding (metadata basis (t:=t)) := (RepresentedPowerTable.encoding (presentation basis) t).list

def productTable (m:ℕ) : metadata basis (t:=t) :=
  RepresentedPowerTable.table (presentation basis) (FixedRealRootRestriction.equalityMachine basis)
    (wordProductMachine basis A) (wordProductMachine basis B) m

theorem fp_productTable : FP BitEncoding.unaryNat (metaEncoding basis (t:=t)) (productTable basis A B) :=
  RepresentedPowerTable.fp_table _ _ _ _

def prepare {D Q:Type} (occ:D→ℕ) (query:ℕ→D→Q) (a:D) : metadata basis (t:=t)×List Q :=
  let rs:=productTable basis A B (occ a)
  (rs,positiveSequence query (rs.length,a))

theorem fp_prepare {D Q:Type} (ed:BitEncoding D) (eq:BitEncoding Q)
    (occ:D→ℕ) (query:ℕ→D→Q) (ho:FP ed BitEncoding.unaryNat occ)
    (hq:FP (BitEncoding.unaryNat.prod ed) eq (fun p=>query p.1 p.2)) :
    FP ed ((metaEncoding basis (t:=t)).prod eq.list) (prepare basis A B occ query) := by
  have ht:=ho.comp (fp_productTable basis A B)
  have hn:=ht.comp (ListUnaryLengthMachine.fp_length (RepresentedPowerTable.encoding (presentation basis) t))
  exact ht.pair ((hn.pair (fp_id ed)).comp (fp_positiveSequence ed eq query hq))

def recover (p:metadata basis (t:=t)×List (ValidCode (presentation basis))) : Code n e :=
  FixedRealInterpolationRecovery.recover basis A (p.1,p.2.map Subtype.val)

theorem fp_recover : FP ((metaEncoding basis (t:=t)).prod (validEncoding (presentation basis)).list)
    (encoding n e) (recover basis A) := by
  have hv:FP (validEncoding (presentation basis)) (encoding n e) Subtype.val:=fp_code_view _ _ _ (fun _=>rfl)
  exact (((fp_fst _ _).pair ((fp_snd _ _).comp (ListMapMachines.fp_map _ _ _ hv))).comp
    (FixedRealInterpolationRecovery.fp_recover basis A))

theorem answer_values {Q:Type} (qs:List Q) (bs:List (ValidCode (presentation basis))) (valueQ:Q→K)
    (h:List.Forall₂ (fun q b=>True ∧ validValue (presentation basis) b=valueQ q) qs bs) :
    (bs.map Subtype.val).map (value basis)=qs.map valueQ := by
  induction h with
  | nil=>rfl
  | @cons q b qs bs hrel hrest ih=>
    simp only [List.map_cons]
    exact congrArg₂ List.cons hrel.2 ih

/-- Interpolation over unrestricted valid oracle representatives with actual
reply-volume work accounting. Query number/size depend only on the input. -/
def reduction {D Q:Type} (ed:BitEncoding D) (eq:BitEncoding Q)
    (nd:BitEncoding.Normalizer ed) (H:D→Prop) (HQ:Q→Prop)
    (target:D→K) (source:Q→K) (occ:D→ℕ) (query:ℕ→D→Q)
    (ho:FP ed BitEncoding.unaryNat occ)
    (hq:FP (BitEncoding.unaryNat.prod ed) eq (fun p=>query p.1 p.2))
    (legal:∀a,H a→∀s,1≤s→HQ (query s a))
    (identity:∀a,H a→LagrangeRecovery.evaluateReplacement
      (ExponentProductTables.sourceNode A B (occ a)) (ExponentProductTables.targetNode A B (occ a))
      (fun h=>source (query (h.val+1) a))=target a) :
    Reduction ((presentation basis).problem ed H target) ((presentation basis).problem eq HQ source) := by
  let P:=presentation basis
  have hc:∀a,H a→∀bs,List.Forall₂ (fun q b=>P.validated.valid b ∧ P.validated.value b=source q)
      (prepare basis A B occ query a).2 bs→
      P.valid (recover basis A ((prepare basis A B occ query a).1,bs)) ∧
      P.value (recover basis A ((prepare basis A B occ query a).1,bs))=target a := by
    intro a ha bs hbs
    let rs:=productTable basis A B (occ a)
    have hvals:((bs.map Subtype.val).map (value basis))=
        List.ofFn (fun i:Fin rs.length=>source (query (i.val+1) a)) := by
      rw [answer_values basis _ bs source hbs]
      change ((List.range rs.length).map (fun i=>query (i+1) a)).map source=_
      rw [List.map_map,RepresentedInterpolationMatrices.range_map_ofFn]
      rfl
    have hy:∀c∈bs.map Subtype.val,Valid n c:=by
      intro c hc
      obtain ⟨b,hb,rfl⟩:=List.mem_map.mp hc
      exact b.property
    have hr:=FixedRealInterpolationRecovery.recover_correct basis A (rs,bs.map Subtype.val)
      (RepresentedPowerTable.table_word_value _ _ _ _ _)
      (RepresentedPowerTable.table_sourceNode_injective _ _ _ _ _)
      (RepresentedPowerTable.table_sourceNode_nonzero _ _ _ _ _) hy _ hvals
    refine ⟨hr.1,hr.2.trans ?_⟩
    rw [RepresentedPowerTable.evaluateReplacement_table P rs _
      (RepresentedPowerTable.table_semantics _ _ _ _ _) (fun s=>source (query (s+1) a))]
    exact identity a ha
  have hlegal:∀a,H a→∀q∈(prepare basis A B occ query a).2,HQ q := by
    intro a ha q hq
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp hq
    exact legal a ha (i+1) (by omega)
  have r:=presentationPipeline P.validated P ed (metaEncoding basis (t:=t)) eq nd
    (BitEncoding.listNormalizer (RepresentedPowerTable.normalizer P t)) H HQ target source
    (prepare basis A B occ query) (recover basis A) (fp_prepare basis A B ed eq occ query ho hq)
    (fp_recover basis A) hlegal hc
  simpa only [Presentation.validated_problem] using r

end PlanarHom.FixedRealInterpolationPipeline
