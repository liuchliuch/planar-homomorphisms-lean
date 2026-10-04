import PlanarHom.MainSupportFiniteSource
import PlanarHom.WeightedActualQuotientSource

/-! Exact recovered same-input color transport, including original output codec. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode RootedRestriction Structures
variable {q r : ℕ}

/-- A fixed color chart changes no graph, edge, loop, or isolated vertex. -/
def mainColorLanguage (L : RealLanguage q 1 0) (e : Fin r≃Fin q) : RealLanguage r 1 0 where
  matrices := fun _ i j=>L.matrices 0 (e i) (e j)
  unaries := Fin.elim0
  weights := fun i=>L.weights (e i)
  matrices_algebraic := fun _ i j=>L.matrices_algebraic 0 _ _
  unaries_algebraic := fun u=>u.elim0
  weights_algebraic := fun i=>L.weights_algebraic _

/-- Canonical field descent followed by a genuine same-input color-reindex
machine, ending in exactly the original source problem. -/
def mainColorSourceReduction (L : RealLanguage q 1 0) (e : Fin r≃Fin q) :
    PromisePolyTimeTuringReduction (L.mainColorLanguage e).problem L.problem := by
  have red := ((L.mainColorLanguage e).presentationDescentReduction L.field L.basis
    (fun _:Fin 1=>fun i j=>L.matricesK 0 (e i) (e j)) (fun u:Fin 0=>u.elim0)
    (fun i=>L.weightsK (e i)) (fun _ _ _=>rfl) (fun u=>u.elim0) (fun _=>rfl)).trans
    (ActualTwins.reindexReduction L.basis (L.matricesK 0) L.weightsK e)
  have hm : (fun _:Fin 1=>L.matricesK 0)=L.matricesK := by
    funext l
    exact congrArg L.matricesK (Subsingleton.elim 0 l)
  have hu : (fun u:Fin 0=>(u.elim0:Fin q→L.field))=L.unariesK := by
    funext u
    exact u.elim0
  rw [hm,hu] at red
  exact red

theorem mainColor_rows_injective (L : RealLanguage q 1 0) (e : Fin r≃Fin q)
    (hi : Function.Injective (L.matrices 0)) :
    Function.Injective ((L.mainColorLanguage e).matrices 0) := by
  intro i j h
  apply e.injective
  apply hi
  funext k
  have hh := congrFun h (e.symm k)
  simpa only [mainColorLanguage,Equiv.apply_symm_apply] using hh

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
