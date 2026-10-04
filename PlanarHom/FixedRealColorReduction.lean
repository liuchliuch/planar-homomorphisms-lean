import PlanarHom.RepresentedQueryReduction
import PlanarHom.FixedRealComponentReduction
import PlanarHom.MixedColorEquivalence

/-! Reindexing a fixed finite color domain is the identity graph query in the
represented model, with exactly the same prescribed answer presentation. -/
noncomputable section
namespace PlanarHom.FixedRealColorReduction
open DensePolynomial Complexity RepresentedBit FixedRealExtension
variable {n e:ℕ} {K C D:Type} [Field K] [Algebra (RationalFunction n) K] [Fintype C] [Fintype D]

def homogeneous (basis:Module.Basis (Fin e) (RationalFunction n) K) (order:C≃D)
    (M:Matrix D D K) (w:D→K) :
    Reduction (FixedRealComponents.problem basis (fun _:Fin 1=>fun i j=>M (order i) (order j))
      (fun u:Fin 0=>u.elim0) (fun i=>w (order i)))
      (FixedRealComponents.problem basis (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) := by
  apply queryReduction (presentation basis) MixedCode.encoding MixedCode.encoding MixedCode.normalizer
    (MixedCode.PlanarValid 1 0) (MixedCode.PlanarValid 1 0)
    (MixedCode.totalEvaluation (fun _:Fin 1=>fun i j=>M (order i) (order j)) (fun u:Fin 0=>u.elim0) (fun i=>w (order i)))
    (MixedCode.totalEvaluation (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w) id (fp_id _)
  · exact fun _ h=>h
  · intro g hg
    dsimp only [id_eq]
    rw [MixedCode.totalEvaluation_valid _ _ _ g hg.1,MixedCode.totalEvaluation_valid _ _ _ g hg.1]
    have hh:=MixedCode.evaluate_color_equiv order g hg.1 (fun _:Fin 1=>M) (fun u:Fin 0=>u.elim0) w
    have hu:(fun (l:Fin 0) i=>(l.elim0:D→K) (order i))=(fun l:Fin 0=>(l.elim0:C→K)) := by
      funext l; exact l.elim0
    rw [hu] at hh
    exact hh.symm

end PlanarHom.FixedRealColorReduction
