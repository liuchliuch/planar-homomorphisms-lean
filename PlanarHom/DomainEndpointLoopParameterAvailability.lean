import PlanarHom.EndpointLoopParameterAvailability
import PlanarHom.RestrictedParameterizedScalarReduction
import PlanarHom.RestrictedParameterizedSchurReduction
import PlanarHom.DomainEndpointLoopAvailability
import PlanarHom.DomainDistanceKernelAvailability

/-! The uniformly parameterized endpoint-loop family on the exact original
domain records. Source loop and path permissions are explicit; a global source
matrix discharges them without restricting old endpoint domains. -/
noncomputable section
namespace PlanarHom.DomainEndpointLoopParameterAvailability
open Complexity Complexity.MixedCode FiniteLanguageAliases PrescribedDomains EndpointLoopMachines
open ParameterizedAppendSchurReduction
variable {K : IntermediateField ℚ ℝ} [FiniteDimensional ℚ K]
variable {dimension q b u d : ℕ}

theorem word_policy (B : Fin b→Fin d→Fin d→Prop) (old : Fin b) :
    ∀i x y,appendOne B (B old) i x y→∀j∈words b i,
      appendOne (appendOne B (B old)) (B old) j x y := by
  intro i
  refine Fin.lastCases ?_ (fun r=>?_) i
  · intro x y h j hj
    rw [appendOne_aux] at h
    simp only [words,Fin.lastCases_last,List.mem_cons,List.mem_nil_iff,or_false] at hj
    rcases hj with rfl|rfl
    · change appendOne (appendOne B (B old)) (B old) (Fin.castAdd 1 (Fin.last b)) x y
      rw [appendOne_old,appendOne_aux]
      exact h
    · simpa only [appendOne_aux] using h
  · intro x y h j hj
    simp only [words,Fin.lastCases_castSucc,List.mem_singleton] at hj
    subst j
    change appendOne B (B old) (Fin.castAdd 1 r) x y at h
    rw [appendOne_old] at h
    change appendOne (appendOne B (B old)) (B old) (Fin.castAdd 1 (Fin.castAdd 1 r)) x y
    rw [appendOne_old,appendOne_old]
    exact h

def targetProblem (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (k : ℕ) (c : K) : PromiseProblem :=
  RestrictedMatrixFamilyReduction.targetProblem basis BitEncoding.rat M (extendedUnaries U D) (fun _=>1)
    (EndpointLoopParameterAvailability.family (M old) k c) (fun x : ℚ=>0<x)
    (EncodedGraph (appendOne B (B old)) T)

def reduction_of_pathTyping (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (k : ℕ) (c : K) (full : Fin d) (hfull : D full=Set.univ)
    (hloop : ∀x,B old x x) (hpath : ∀x y,B old x y→PathDomainTyping B old full x y)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (DistanceKernelAvailability.graph (M old)).Connected)
    (hedge : ∀i j,(DistanceKernelAvailability.graph (M old)).Adj i j→
      0<EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis M U (fun _=>1) D B T) base) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D B T old k c) base := by
  let A:=decorated (M old) k
  let expanded:=appendOne M A
  let PB:=appendOne B (B old)
  let ER:=DistanceKernelEvaluationMachines.matrix (K:=K) (DistanceKernelAvailability.graph (M old))
  let HT:=EncodedGraph PB T
  let HS:=EncodedGraph (appendOne PB (B old)) T
  have he : expanded (Fin.castAdd 1 old)=M old:=appendOne_old M A old
  have heB : PB (Fin.castAdd 1 old)=B old:=appendOne_old B (B old) old
  let kernel:=DomainDistanceKernelAvailability.reduction_of_pathTyping basis expanded U D PB T
    (Fin.castAdd 1 old) full hfull
    (by intro x y h; simpa only [PathDomainTyping,heB] using hpath x y (by simpa only [heB] using h))
    (by simpa only [he] using hA) (by simpa only [he] using hG) (by simpa only [he] using hedge)
  have kernel' : PromisePolyTimeTuringReduction
      (RestrictedMatrixFamilyReduction.targetProblem basis BitEncoding.rat expanded (extendedUnaries U D)
        (fun _=>1) ER (fun x : ℚ=>0<x) HS)
      (domainEvaluationProblem basis expanded U (fun _=>1) D PB T) := by
    simpa only [DomainDistanceKernelAvailability.targetProblem,he,heB] using kernel
  let simulation:=kernel'.trans ((EndpointLoopMachines.domainReduction basis M U (fun _=>1)
    D B T old k hloop).trans available)
  let product:=(RestrictedParameterizedSchurReduction.reduction basis BitEncoding.rat M A
    (extendedUnaries U D) (fun _=>1) ER (fun x : ℚ=>0<x) HT HS
    (fun _ h=>(h.planarValid _ _).1)
    (fun _ h=>h.expandBinaryWords (words b) (word_policy B old)) base simulation).trans simulation
  exact (RestrictedParameterizedScalarReduction.reduction basis BitEncoding.rat M (extendedUnaries U D)
    (fun _=>1) (fun x i j=>A i j*ER x i j) (fun x : ℚ=>0<x) c HT
    (fun _ h=>(h.planarValid _ _).1) base product).trans product

def reduction_global (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Fin b→Matrix (Fin q) (Fin q) K) (U : Fin u→Fin q→K)
    (D : Fin d→Set (Fin q)) (B : Fin b→Fin d→Fin d→Prop) (T : Fin u→Fin d→Prop)
    (old : Fin b) (k : ℕ) (c : K) (full : Fin d) (hfull : D full=Set.univ)
    (hA : (SpectralFieldPresentation.realMatrix (M old)).PosDef)
    (hG : (DistanceKernelAvailability.graph (M old)).Connected)
    (hedge : ∀i j,(DistanceKernelAvailability.graph (M old)).Adj i j→
      0<EntropyCompletion.matrixLog (SpectralFieldPresentation.realMatrix (M old)) i j)
    (base : PromiseProblem) (available : PromisePolyTimeTuringReduction
      (domainEvaluationProblem basis M U (fun _=>1) D (withGlobalMatrix B old) T) base) :
    PromisePolyTimeTuringReduction (targetProblem basis M U D (withGlobalMatrix B old) T old k c) base :=
  reduction_of_pathTyping basis M U D (withGlobalMatrix B old) T old k c full hfull
    (fun _=>withGlobalMatrix_self B old _ _)
    (fun x y _=>withGlobalMatrix_pathTyping B old full x y) hA hG hedge base available

end PlanarHom.DomainEndpointLoopParameterAvailability
