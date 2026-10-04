import PlanarHom.BodyCorollariesClosed

/-! NEW literal empty/nonempty answer clause of Corollary 11.2. -/
noncomputable section
set_option autoImplicit false
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode
variable {q : ℕ}

theorem zero_vertex_weights_evaluate (L : RealLanguage q 1 0) (hw : ∀i,L.weights i=0)
    (g : MixedCode) (hg : g.Valid 1 0) :
    g.evaluate hg L.matricesK L.unariesK L.weightsK=if g.vertices=0 then 1 else 0 := by
  have hm:L.matricesK=(fun _ : Fin 1=>L.matricesK 0):=funext (fun l=>congrArg L.matricesK (Subsingleton.elim l 0))
  have hu:L.unariesK=(fun u : Fin 0=>u.elim0):=funext (fun u=>u.elim0)
  have hz:L.weightsK=(fun _=>0):=funext (fun i=>Subtype.ext (hw i))
  rw [hm,hu,hz,evaluate_homogeneous]
  by_cases hn:g.vertices=0
  · rw [if_pos hn]
    letI : IsEmpty (Fin g.vertices):=⟨fun v=>by have h:=v.isLt; omega⟩
    letI : IsEmpty (Fin g.edges.length):=⟨fun e=>isEmptyElim ((g.toMultiGraph hg).src e)⟩
    simp [MultiGraph.partition,MultiGraph.assignmentWeight]
  · rw [if_neg hn]
    letI : Nonempty (Fin g.vertices):=⟨⟨0,by omega⟩⟩
    exact (g.toMultiGraph hg).partition_zero_vertexWeights (L.matricesK 0)

theorem empty_surviving_evaluate (L : RealLanguage q 1 0) (hw : ∀i,0≤L.weights i)
    (hS : ∀i,¬0<L.weights i) (g : MixedCode) (hg : g.Valid 1 0) :
    g.evaluate hg L.matricesK L.unariesK L.weightsK=if g.vertices=0 then 1 else 0 :=
  L.zero_vertex_weights_evaluate (fun i=>le_antisymm (le_of_not_gt (hS i)) (hw i)) g hg

end PlanarHom.AlgebraicProductInterpolation.RealLanguage
