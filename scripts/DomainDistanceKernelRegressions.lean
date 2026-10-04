import PlanarHom.DomainDistanceKernelRealAvailability

noncomputable section
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.PrescribedDomains PlanarHom.LogarithmicSupport
open PlanarHom.AlgebraicProductInterpolation

private def domains42 (i : Fin 3) : Set (Fin 2) :=
  if i.val=1 then Set.univ else if i.val=0 then {0} else {1}
private def companions42 : Fin 2 → Fin 3 → Fin 3 → Prop := fun _ x y => x=0 ∧ y=0
private def unaries42 : Fin 0 → Fin 3 → Prop := fun i => Fin.elim0 i

example : PathDomainTyping (withGlobalMatrix companions42 1) 1 1 0 2 :=
  withGlobalMatrix_pathTyping _ _ _ _ _
example : ¬ withGlobalMatrix companions42 1 0 0 2 := by
  norm_num [withGlobalMatrix,companions42]
  decide
example : domains42 0 ≠ domains42 1 := by
  intro h
  have hp : (1 : Fin 2) ∈ domains42 1 := by simp [domains42]
  rw [← h] at hp
  simp [domains42] at hp

-- An alternate unary sample word normalizes by its actual decoded length.
example : DynamicMatrixFamilySource.queryEncoding.decode
    (BitEncoding.frame [false,false] ++ encoding.encode (MixedCode.mk 1 [(0,0,0)] [])) =
      some (2, MixedCode.mk 1 [(0,0,0)] []) := by
  simp [DynamicMatrixFamilySource.queryEncoding, BitEncoding.prod, BitEncoding.unaryNat, encoding.decode_encode]

-- The full endpoint retains the original domain-restricted source oracle.
example (L : RealLanguage 2 2 0) (hunit : ∀ i, L.weights i=1)
    (hH : (L.matrices 1).PosDef) (hc : (logSupport (L.matrices 1)).Connected)
    (hp : ∀ i j, (logSupport (L.matrices 1)).Adj i j →
      0 < EntropyCompletion.matrixLog (L.matrices 1) i j)
    (base : PromiseProblem)
    (available : PromisePolyTimeTuringReduction
      (L.domainProblem domains42 (withGlobalMatrix companions42 1) unaries42) base) :
    PromisePolyTimeTuringReduction
      (L.domainDistanceKernelTargetProblem domains42 (withGlobalMatrix companions42 1) unaries42 1) base :=
  L.lemma42_global_domain hunit domains42 companions42 unaries42 1 1
    (by simp [domains42]) hH hc hp base available

#print axioms UniformDomainPowerSimulation.reduction
#print axioms RestrictedMatrixFamilyReduction.reduction
#print axioms DomainDistanceKernelAvailability.target_valid_iff
#print axioms AlgebraicProductInterpolation.RealLanguage.lemma42_global_domain
