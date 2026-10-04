import PlanarHom.MixedParallelSemantics
import Mathlib.Data.Matrix.Basis
import Mathlib.LinearAlgebra.Matrix.Reindex
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.Complexity.MixedCode
variable {C D R:Type} [Fintype C] [Fintype D] [CommSemiring R] {bt ut:ℕ}
theorem evaluate_color_equiv (e:C≃D) (g:MixedCode) (hg:g.Valid bt ut)
    (M:Fin bt→Matrix D D R) (U:Fin ut→D→R) (w:D→R) :
    g.evaluate hg (fun l i j=>M l (e i) (e j)) (fun l i=>U l (e i)) (fun i=>w (e i))=
      g.evaluate hg M U w := by
  unfold evaluate
  apply Fintype.sum_equiv (Equiv.piCongrRight (fun _ : Fin g.vertices=>e))
  intro σ
  congr 2
theorem matrix_power_color_equiv [DecidableEq C] [DecidableEq D]
    (e:C≃D) (B:Matrix D D R) (n:ℕ) :
    (show Matrix C C R from fun i j=>B (e i) (e j))^n=fun i j=>(B^n) (e i) (e j) := by
  exact ((Matrix.reindexAlgEquiv R R e.symm).map_pow B n).symm
end PlanarHom.Complexity.MixedCode
