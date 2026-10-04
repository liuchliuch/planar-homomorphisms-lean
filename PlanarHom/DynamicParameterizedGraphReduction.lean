import PlanarHom.ParameterizedGraphReduction
import PlanarHom.UnaryNatConversionMachine

/-! NEW actual raw-unary-input compiler for a parameterized graph oracle.
All successful raw unary and graph encodings are normalized, not excluded. -/
noncomputable section
namespace PlanarHom.DynamicParameterizedGraphReduction
open Complexity Complexity.MixedCode FiniteLanguageAliases MachineComposition
variable {X Meta K : Type} [Field K] [Algebra ℚ K]
variable {dimension q bt ut bs us : ℕ}

def rawView (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (raw : Bits)
    (h : (DynamicMatrixFamilySource.problem basis M U (fun _=>1) F).valid raw) :
    BitEncoding.ValidWord DynamicMatrixFamilySource.queryEncoding :=
  ⟨raw, by obtain ⟨p,hp,_⟩:=h; exact ⟨p,hp⟩⟩

theorem rawView_spec (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (raw : Bits)
    (h : (DynamicMatrixFamilySource.problem basis M U (fun _=>1) F).valid raw) :
    1 ≤ (rawView basis M U F raw h).value.1 ∧
      (rawView basis M U F raw h).value.2.PlanarValid (bt+1) ut := by
  obtain ⟨p,hp,hn,hg⟩:=h
  have hv := BitEncoding.ValidWord.value_eq
    (w:=rawView basis M U F raw ⟨p,hp,hn,hg⟩) hp
  rw [hv]
  exact ⟨hn,hg⟩

def reductionOfPipeline
    (basis : Module.Basis (Fin dimension) ℚ K) (ex : BitEncoding X) (em : BitEncoding Meta)
    (M : Fin bt → Matrix (Fin q) (Fin q) K) (U : Fin ut → Fin q → K)
    (N : Fin bs → Matrix (Fin q) (Fin q) K) (V : Fin us → Fin q → K)
    (F : ℕ → Matrix (Fin q) (Fin q) K) (G : X → Matrix (Fin q) (Fin q) K)
    (allowed : X → Prop)
    (prepare : ℕ×MixedCode → Meta×List (X×MixedCode)) (recover : Meta×List K → K)
    (hp : FP DynamicMatrixFamilySource.queryEncoding (em.prod (ex.prod encoding).list) prepare)
    (hr : FP (em.prod (numberFieldEncoding basis).list) (numberFieldEncoding basis) recover)
    (hq : ∀p,1≤p.1→p.2.PlanarValid (bt+1) ut→∀query∈(prepare p).2,
      allowed query.1 ∧ query.2.PlanarValid (bs+1) us)
    (correct : ∀p,1≤p.1→p.2.PlanarValid (bt+1) ut→
      recover ((prepare p).1,(prepare p).2.map
        (ParameterizedMatrixEvaluation.answer N V (fun _=>1) G))=
      DynamicMatrixFamilySource.answer M U (fun _=>1) F p)
    (base : PromiseProblem)
    (simulation : PromisePolyTimeTuringReduction
      (ParameterizedMatrixEvaluation.problem basis ex N V (fun _=>1) G allowed) base) :
    PromisePolyTimeTuringReduction (DynamicMatrixFamilySource.problem basis M U (fun _=>1) F)
      (ParameterizedMatrixEvaluation.problem basis ex N V (fun _=>1) G allowed) := by
  let target:=DynamicMatrixFamilySource.problem basis M U (fun _=>1) F
  let source:=ParameterizedMatrixEvaluation.problem basis ex N V (fun _=>1) G allowed
  let pre:=composeComputers (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (Classical.choice hp)
  apply nonadaptiveReduction (p:=simulation.outputPolynomial)
    (BitEncoding.ValidWord.encoding DynamicMatrixFamilySource.queryEncoding) em
    (ex.prod encoding) (numberFieldEncoding basis) (numberFieldEncoding basis)
    target source (prepare ∘ BitEncoding.ValidWord.value)
    (ParameterizedMatrixEvaluation.answer N V (fun _=>1) G) recover pre
    (Classical.choice hr) (rawView basis M U F) (fun _ _=>rfl)
  · intro raw h query hquery
    have hs:=rawView_spec basis M U F raw h
    have hvalid:=hq _ hs.1 hs.2 query hquery
    exact ⟨ParameterizedGraphReduction.canonicalView query,
      ParameterizedGraphReduction.canonicalView_encode ex query,hvalid.1,
      by simpa only [ParameterizedGraphReduction.canonicalView_value] using hvalid.2⟩
  · intro query _
    exact ParameterizedGraphReduction.value_encode basis ex N V (fun _=>1) G allowed query
  · intro raw h
    let z:=rawView basis M U F raw h
    have hs:=rawView_spec basis M U F raw h
    have hc:=correct z.value hs.1 hs.2
    change (numberFieldEncoding basis).encode (recover
      ((prepare z.value).1,(prepare z.value).2.map
        (ParameterizedMatrixEvaluation.answer N V (fun _=>1) G)))=target.value raw
    rw [hc]
    have hd : DynamicMatrixFamilySource.queryEncoding.decode raw = some z.value :=
      BitEncoding.ValidWord.decode_raw z
    simp only [target,DynamicMatrixFamilySource.problem,encodedFunction,hd]
  · exact simulation.output_length_bound

end PlanarHom.DynamicParameterizedGraphReduction
