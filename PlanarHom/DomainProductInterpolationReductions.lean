import PlanarHom.ProductInterpolationReductions
import PlanarHom.PrescribedDomainQueryPromises
import PlanarHom.PromiseReductionTransport

/-! Lemma3.1 on the exact prescribed-domain input model from Definition2.1.
Reserved indicators remain intrinsic metadata; no pinning availability is used. -/
namespace PlanarHom.Complexity.MixedCode
noncomputable section
open PlanarHom.PrescribedDomains PlanarHom.ProductCompatibility
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K]
variable {q dimension binaryTypes unaryTypes domainTypes : ℕ}

noncomputable def domainBinaryProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M M' : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (D : Fin domainTypes→Set (Fin q))
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) (selected : Fin binaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→M' l=M l)
    (hzero : ∀i j,M selected i j=0→M' selected i j=0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q=>M selected p.1 p.2)
      (fun p : Fin q × Fin q=>M' selected p.1 p.2)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M' U w D B T)
      (domainEvaluationProblem basis M U w D B T):=by
  let r:=binaryProductReductionOn basis M M' (extendedUnaries U D) w selected (EncodedGraph B T)
    (fun _ h=>(h.planarValid B T).1) (fun _ h n=>h.parallelLabel B T selected.val n)
    hunchanged hzero hproducts
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph B T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h)
    (fun _ _=>rfl) (fun _ _=>rfl)

noncomputable def domainUnaryProductReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U U' : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (D : Fin domainTypes→Set (Fin q))
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) (selected : Fin unaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→U' l=U l)
    (hzero : ∀i,U selected i=0→U' selected i=0)
    (hproducts : HasProductMaps (U selected) (U' selected)) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U' w D B T)
      (domainEvaluationProblem basis M U w D B T):=by
  let chosen : Fin (unaryTypes+domainTypes):=selected.castAdd domainTypes
  have hext : ∀l : Fin (unaryTypes+domainTypes),l.val≠chosen.val→extendedUnaries U' D l=extendedUnaries U D l:=by
    intro l
    refine Fin.addCases ?_ ?_ l
    · intro i hi
      simpa [extendedUnaries] using hunchanged i (by simpa [chosen] using hi)
    · intro i _
      simp [extendedUnaries]
  have hs : extendedUnaries U D chosen=U selected:=by simp [extendedUnaries,chosen]
  have hs' : extendedUnaries U' D chosen=U' selected:=by simp [extendedUnaries,chosen]
  let r:=unaryProductReductionOn basis M (extendedUnaries U D) (extendedUnaries U' D) w chosen
    (EncodedGraph B T) (fun _ h=>(h.planarValid B T).1)
    (fun _ h n=>h.parallelUnaryLabel B T selected.val n selected.isLt) hext
    (by simpa only [hs,hs'] using hzero) (by simpa only [hs,hs'] using hproducts)
  exact r.transport _ _
    (fun raw h=>(encodedInput_iff_graph B T raw).mp h)
    (fun raw h=>(encodedInput_iff_graph B T raw).mpr h)
    (fun _ _=>rfl) (fun _ _=>rfl)

/-- Genuine joint availability closure on the same fixed permitted domains. -/
noncomputable def domainBinaryProduct_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M M' : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (D : Fin domainTypes→Set (Fin q))
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) (selected : Fin binaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→M' l=M l)
    (hzero : ∀i j,M selected i j=0→M' selected i j=0)
    (hproducts : HasProductMaps (fun p : Fin q × Fin q=>M selected p.1 p.2)
      (fun p : Fin q × Fin q=>M' selected p.1 p.2))
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T) base) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M' U w D B T) base:=
  (domainBinaryProductReduction basis M M' U w D B T selected hunchanged hzero hproducts).trans available

noncomputable def domainUnaryProduct_joint (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin binaryTypes→Matrix (Fin q) (Fin q) K) (U U' : Fin unaryTypes→Fin q→K) (w : Fin q→K)
    (D : Fin domainTypes→Set (Fin q))
    (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
    (T : Fin unaryTypes→Fin domainTypes→Prop) (selected : Fin unaryTypes)
    (hunchanged : ∀l,l.val≠selected.val→U' l=U l)
    (hzero : ∀i,U selected i=0→U' selected i=0)
    (hproducts : HasProductMaps (U selected) (U' selected))
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U w D B T) base) :
    PromisePolyTimeTuringReduction (domainEvaluationProblem basis M U' w D B T) base:=
  (domainUnaryProductReduction basis M U U' w D B T selected hunchanged hzero hproducts).trans available

end
end PlanarHom.Complexity.MixedCode
