import PlanarHom.RawPartitionOutputBounds
import PlanarHom.PrescribedDomainTyping

/-! The ordinary raw-code planar mixed-evaluation promise, and its exact
prescribed-domain restriction. All successful alternate encodings are admitted. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open Classical
variable {C K : Type} [Fintype C] [Field K] [Algebra ℚ K]
variable {dimension binaryTypes unaryTypes : ℕ}

/-- Invalid decoding/ranges have an explicit total fallback, irrelevant to the
promise. No planarity decision or arbitrary invalid oracle advice is used. -/
def evaluationValue (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K) (bits : Bits) : Bits:=
  match encoding.decode bits with
  | none=>[]
  | some g=>if hg:g.Valid binaryTypes unaryTypes then
      (numberFieldEncoding basis).encode (g.evaluate hg M U w) else []

def evaluationProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K) : PromiseProblem:=
  ⟨PlanarInput binaryTypes unaryTypes,evaluationValue basis M U w⟩

theorem evaluationValue_decode (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K)
    (bits : Bits) (g : MixedCode) (hd : encoding.decode bits=some g) (hg : g.Valid binaryTypes unaryTypes) :
    evaluationValue basis M U w bits=(numberFieldEncoding basis).encode (g.evaluate hg M U w):=by
  simp only [evaluationValue,hd,dif_pos hg]

@[simp] theorem evaluationValue_encode (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K)
    (g : MixedCode) (hg : g.Valid binaryTypes unaryTypes) :
    evaluationValue basis M U w (encoding.encode g)=(numberFieldEncoding basis).encode (g.evaluate hg M U w):=
  evaluationValue_decode basis M U w _ g (encoding.decode_encode g) hg

theorem evaluationProblem_output_bound (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K) :
    ∃p : Polynomial ℕ,∀bits,(evaluationProblem basis M U w).valid bits→
      ((evaluationProblem basis M U w).value bits).length≤p.eval bits.length:=by
  obtain ⟨p,hp⟩:=PlanarHom.PartitionOutputBounds.exists_polynomial_raw_mixed_evaluation_length_bound basis M U w
  refine ⟨p,?_⟩
  intro bits h
  obtain ⟨g,hd,hg⟩:=h
  change (evaluationValue basis M U w bits).length≤_
  rw [evaluationValue_decode basis M U w bits g hd hg.1]
  exact hp bits g hg.1 hd

/-- Same raw values, restricted to exactly the allowed prescribed-domain input
representation. Reserved indicators encode metadata, not newly available labels. -/
def domainEvaluationProblem {domainTypes : ℕ} (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K)
    (D : Fin domainTypes→Set C)
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) : PromiseProblem:=
  ⟨PlanarHom.PrescribedDomains.EncodedInput B T,
    evaluationValue basis M (PlanarHom.PrescribedDomains.extendedUnaries U D) w⟩

theorem domainEvaluationProblem_output_bound {domainTypes : ℕ}
    (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix C C K) (U : Fin unaryTypes→C→K) (w : C→K)
    (D : Fin domainTypes→Set C)
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) :
    ∃p : Polynomial ℕ,∀bits,(domainEvaluationProblem basis M U w D B T).valid bits→
      ((domainEvaluationProblem basis M U w D B T).value bits).length≤p.eval bits.length:=by
  obtain ⟨p,hp⟩:=evaluationProblem_output_bound basis M (PlanarHom.PrescribedDomains.extendedUnaries U D) w
  exact ⟨p,fun bits h=>hp bits h.planarInput⟩

end
end PlanarHom.Complexity.MixedCode
