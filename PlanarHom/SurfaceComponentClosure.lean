import PlanarHom.SurfaceComponentTractability
import PlanarHom.BipartiteRankTwoEvaluationMachines
import PlanarHom.TractableBlockComposition

/-! NEW actual supplied-row block computers. Connected values are evaluated
by their original finite programs, summed over fixed target blocks, then
multiplied over the computed occurrence components with inherited rows. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SurfaceRowEvaluation
open Complexity
variable {C B K : Type} [Fintype C] [Fintype B] [Field K] [Algebra ℚ K]
variable {dimension k l : ℕ}

theorem bipartite_inFP (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K)
    (a μ : Fin k→K) (b ν : Fin l→K) :
    Evaluable ambient basis (fun _:Fin 1=>BipartiteRankTwoTractability.matrix a b)
      (fun u:Fin 0=>u.elim0) (Sum.elim μ ν) := by
  apply evaluable_of_connected ambient basis _ _ _
  have hv : FP (encoding.restrict (ConnectedValid 1 0 ambient)) MixedCode.encoding
      (fun p:{p:Input // ConnectedValid 1 0 ambient p}=>p.val.1) :=
    (fp_code_view _ encoding Subtype.val (fun _=>rfl)).comp
      (PairProjectionMachines.fp_fst MixedCode.encoding PlanarityRowFaceCode.rowsCode)
  exact (hv.comp (BipartiteRankTwoTractability.fp_evaluateConnected basis a μ b ν)).congr
    (fun p=>BipartiteRankTwoTractability.evaluateConnected_correct p.val.1 (graph_valid p.property.1)
      p.property.2.1 p.property.2.2 a μ b ν)

theorem fibers_inFP (ambient : ℕ) (basis : Module.Basis (Fin dimension) ℚ K) (block : C→B)
    (M : Matrix C C K) (hs : ∀i j,M i j=M j i)
    (hzero : ∀i j,block i≠block j→M i j=0) (w : C→K)
    (h : ∀b:B,Evaluable ambient basis
      (fun _:Fin 1=>fun i j:{i // block i=b}=>M i.val j.val)
      (fun u:Fin 0=>u.elim0) (fun i=>w i.val)) :
    Evaluable ambient basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w := by
  apply evaluable_of_connected ambient basis _ _ _
  have hsum := FixedFieldPolynomialMachines.fp_sum basis
    (encoding.restrict (ConnectedValid 1 0 ambient)) Finset.univ
    (fun (p:{p:Input // ConnectedValid 1 0 ambient p}) (b:B)=>
      p.val.1.evaluate (graph_valid p.property.1)
        (fun _:Fin 1=>fun i j:{i // block i=b}=>M i.val j.val)
        (fun u:Fin 0=>u.elim0) (fun i=>w i.val)) (by
      intro b _
      exact connected_of_evaluable ambient basis _ _ _ (h b))
  exact hsum.congr (fun p=>(TractableBlockComposition.evaluate_eq_sum_fibers p.val.1
    (graph_valid p.property.1) p.property.2.1 p.property.2.2 M hs block hzero w).symm)

end PlanarHom.SurfaceRowEvaluation
