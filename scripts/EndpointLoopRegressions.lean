import PlanarHom.DomainEndpointLoopAvailability
import PlanarHom.BooleanFamilyPosDef

set_option maxHeartbeats 1000000
noncomputable section
open Classical
open PlanarHom PlanarHom.Complexity PlanarHom.Complexity.MixedCode
open PlanarHom.EndpointLoopMachines PlanarHom.BooleanPDNormalization

private def markedLoop : MixedCode := ⟨1,[(0,0,1)],[(0,0)]⟩
private theorem markedLoop_valid : markedLoop.Valid 2 1 := by simp [markedLoop,Valid]
private theorem transformed_valid : (transform (0 : Fin 1) 2 markedLoop).Valid 1 1 := by
  norm_num [transform,addLoopsAt,loopVertices,GraphDegreeMachines.endpoints,markedLoop,Valid,
    relabelBinary,FiniteLabelLookupMachines.lookup,FiniteLabelLookupMachines.finTable,dropAux]

private def repeated : MixedCode := ⟨3,[(0,1,1),(0,1,1),(1,2,0)],[(2,0)]⟩
example : loopVertices 1 2 markedLoop=[0,0,0,0] := by decide
example : (transform (0 : Fin 1) 2 markedLoop).edges=List.replicate 5 (0,0,0) := by decide
example : (transform (0 : Fin 1) 0 markedLoop).edges=[(0,0,0)] := by decide
example : (transform (0 : Fin 1) 1 repeated).edges=
    [(0,1,0),(0,1,0),(1,2,0),(0,0,0),(1,1,0),(0,0,0),(1,1,0)] := by decide
example : (transform (0 : Fin 1) 1 repeated).unaries=[(2,0)] := by decide
example : (transform (0 : Fin 1) 1 repeated).vertices=3 := rfl

example : decorated (3 • normalForm 2 (1/3)) 1 false true=(9 : ℝ) := by
  norm_num [decorated,normalForm,Matrix.smul_apply,smul_eq_mul]
example : decorated (normalForm 2 (1/3)) 1 false false=(8 : ℝ) := by
  norm_num [decorated,normalForm]
example : decorated (normalForm 2 (1/3)) 1 false true=(1/3 : ℝ) := by
  norm_num [decorated,normalForm]
example : (normalForm ((2 : ℝ)^3) ((1/3)*(1/2))).PosDef := by
  exact BooleanFamilyPosDef.parameterFactor_posDef 2 (1/3) (1/2)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) 3

-- The zero-dimensional product is a genuine one-color matrix.
example (x : ℝ) (z z' : Fin 0→Bool) :
    CubeTensorExponential.tensor (fun _ : Fin 0=>normalForm ((2 : ℝ)^5) ((1/3)*x)) z z'=1 := by
  simp [CubeTensorExponential.tensor]

example {C R : Type} [Fintype C] [CommSemiring R] (A : Matrix C C R)
    (U : Fin 1→C→R) (w : C→R) :
    (transform (0 : Fin 1) 2 markedLoop).evaluate transformed_valid (fun _ : Fin 1=>A) U w=
      markedLoop.evaluate markedLoop_valid (FiniteLanguageAliases.appendOne (fun _ : Fin 1=>A)
        (decorated A 2)) U w :=
  evaluate_transform 0 2 markedLoop markedLoop_valid (fun _ : Fin 1=>A) U w transformed_valid

example {d : ℕ} (δ : Fin repeated.vertices→Fin d) :
    transform (0 : Fin 1) 1 (PrescribedDomains.withDomains (unaryTypes:=1) repeated δ)=
      PrescribedDomains.withDomains (unaryTypes:=1) (transform (0 : Fin 1) 1 repeated) δ :=
  transform_withDomains 0 1 repeated δ

#print axioms reduction
#print axioms domainReduction
#print axioms evaluate_transform
#print axioms BooleanFamilyPosDef.parameterTensor_posDef
#print axioms BooleanLoopNormalization.source_family
