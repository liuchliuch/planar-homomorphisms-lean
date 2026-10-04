import PlanarHom.SignedBooleanLeafGadget
import PlanarHom.SignedSourceGadgetReductions
import PlanarHom.EdgeGadgetNetworkReduction

/-! Literal cofacial endpoint-leaf substitution on every occurrence, compiled
by the actual finite-template machine. All outputs remain in the source field. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SignedThreeState
open Complexity Complexity.MixedCode PairProjectionMachines FixedGadgetNetwork EdgeSubstitution
variable {K C : Type} [Field K] [Algebra ℚ K] [Fintype C]
variable {dimension u p e : ℕ}

/-- Fixed cofacial gadget substitution uses the proven numeric network
compiler, including loops whose two terminal ports are identified. -/
def homogeneousGadgetReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (G : TwoTerminal (Fin p) (Fin e)) (hG : TwoTerminal.PlanarEdgeGadget G)
    (M : Matrix C C K) (U : Fin u→C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>TwoTerminal.signature G M (fun _=>1)) U (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>M) U (fun _=>1)) := by
  let t := ofColoredTwoTerminal G (fun _ : Fin e=>(0:Fin 1))
  let ts := [t]
  have ht : ∀v∈ts,v.code.Valid 1 u := by
    intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact ofColoredTwoTerminal_valid _ _
  have hb : ∀v∈ts,v.boundary=2 := by
    intro v hv
    obtain rfl := List.mem_singleton.mp hv
    rfl
  have hp : ∀v (hv:v∈ts),TwoTerminal.PlanarEdgeGadget (v.edgeGadget (hb v hv) (ht v hv)) := by
    intro v hv
    obtain rfl := List.mem_singleton.mp hv
    exact ofColoredTwoTerminal_planar _ _ hG
  have hm : interactions ts (fun _:Fin 1=>M) U=
      (fun _:Fin 1=>TwoTerminal.signature G M (fun _=>1)) := by
    funext l
    change Fin 1 at l
    have hl : l=0 := Subsingleton.elim _ _
    subst l
    change templateInteraction t (fun _:Fin 1=>M) U=TwoTerminal.signature G M (fun _=>1)
    rw [templateInteraction_colored]
    rfl
  apply planarReductionOfPipeline basis BitEncoding.bits _ U (fun _=>1)
    (fun _:Fin 1=>M) U (fun _=>1) (fun g=>([],[substitute ts g])) (fun p:Bits×List K=>p.2.sum)
  · exact (fp_const _ BitEncoding.bits []).pair
      (((fp_substitute ts).pair (fp_const _ encoding.list [])).comp (ListMutationMachines.fp_cons encoding))
  · exact (fp_snd _ _).comp (MaterializedFieldListMachines.fp_sum basis)
  · intro g hg query hq
    obtain rfl := List.mem_singleton.mp hq
    exact substitute_planarValid ts ht hb hp g hg
  · intro g hg
    simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,add_zero]
    rw [totalEvaluation_valid _ _ _ _ (substitute_valid ts ht hb g hg.1),
      evaluate_substitute ts ht hb g hg.1,hm]

def leafDecorated (M : Matrix C C K) : Matrix C C K :=
  fun i j=>(∑x,M i x)*M i j*(∑y,M j y)

/-- The explicit three-edge drawing closes all planarity prerequisites. -/
def leafDecorationReduction (basis : Module.Basis (Fin dimension) ℚ K)
    (M : Matrix C C K) (U : Fin u→C→K) :
    PromisePolyTimeTuringReduction
      (evaluationProblem basis (fun _:Fin 1=>leafDecorated M) U (fun _=>1))
      (evaluationProblem basis (fun _:Fin 1=>M) U (fun _=>1)) := by
  have h := homogeneousGadgetReduction basis endpointLeavesFin endpointLeavesFin_planar M U
  have hs : TwoTerminal.signature endpointLeavesFin M (fun _=>1)=leafDecorated M := by
    have he := TwoTerminal.coloredSignature_reindexInternal endpointLeaves finTwoEquiv.symm
      (Equiv.refl (Fin 3)) (fun _=>M) (fun _=>1)
    simp only [Equiv.refl_symm,Equiv.refl_apply,TwoTerminal.coloredSignature_const] at he
    rw [show TwoTerminal.signature endpointLeavesFin M (fun _=>1)=
      TwoTerminal.signature endpointLeaves M (fun _=>1) from he]
    funext i j
    exact endpointLeaves_signature M i j
  rw [hs] at h
  exact h

theorem leafDecorated_booleanMatrix (a b c : K) :
    leafDecorated (booleanMatrix a b c)=
      booleanMatrix (a*(a+b)^2) (b*(a+b)*(b+c)) (c*(b+c)^2) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [leafDecorated,booleanMatrix,Fin.sum_univ_two] <;> ring_nf <;> simp

end PlanarHom.SignedThreeState
