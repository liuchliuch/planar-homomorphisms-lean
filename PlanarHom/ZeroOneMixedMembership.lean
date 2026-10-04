import PlanarHom.ZeroOneMixedSharpP
import PlanarHom.ZeroOneCountSemantics
import PlanarHom.AlgebraicProductInterpolation

/-! NEW exact original-language membership endpoint for Theorem 7.1. The
accepting-path count is transported into the language's actual number field;
unit weights and zero-one entries are the only algebraic premises. -/
noncomputable section
open Classical
namespace PlanarHom.ZeroOneMixedMembership
open Complexity ZeroOneSharpPMembership AlgebraicProductInterpolation

def realRelation {q:ℕ} (L:RealLanguage q 1 0) : Relation q :=
  fun i j=>decide (L.matrices 0 i j=1)

theorem realRelation_matrixK {q:ℕ} (L:RealLanguage q 1 0)
    (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) (i j:Fin q) :
    L.matricesK 0 i j=if realRelation L i j then 1 else 0 := by
  apply Subtype.ext
  rcases h01 i j with h|h <;> simp [realRelation,h]

theorem weightsK_one {q:ℕ} (L:RealLanguage q 1 0) (hunit:∀i,L.weights i=1) :
    L.weightsK=(fun _=>1) := by
  funext i
  apply Subtype.ext
  simpa using hunit i

theorem evaluate_eq_count {q:ℕ} (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1)
    (g:MixedCode) (hg:g.Valid 1 0) :
    g.evaluate hg L.matricesK L.unariesK L.weightsK=
      (ZeroOneSharpPMembership.count q (realRelation L) g.underlying (g.underlying_valid hg):L.field) := by
  have hm:L.matricesK=(fun _:Fin 1=>fun i j=>if realRelation L i j then (1:L.field) else 0) := by
    funext l i j
    have hl:l=0:=Subsingleton.elim _ _
    subst l
    exact realRelation_matrixK L h01 i j
  have hu:L.unariesK=(fun u:Fin 0=>Fin.elim0 u) := by funext u; exact u.elim0
  rw [hm,hu,weightsK_one L hunit,MixedCode.evaluate_homogeneous]
  have hi:=(g.underlyingIncidenceEquiv hg).partition
    (fun i j=>if realRelation L i j then (1:L.field) else 0) (fun _=>1)
  exact hi.symm.trans (ZeroOneSharpPMembership.count_eq_evaluate q (realRelation L) g.underlying (g.underlying_valid hg)).symm

theorem membership {q:ℕ} (L:RealLanguage q 1 0)
    (hunit:∀i,L.weights i=1) (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    ∃f:Bits→ℕ,SharpP f ∧ ∀raw,L.problem.valid raw →
      L.problem.value raw=(numberFieldEncoding L.basis).encode (f raw:L.field) := by
  refine ⟨totalCount q (realRelation L),totalCount_sharpP q (realRelation L),?_⟩
  intro raw hr
  obtain ⟨g,hd,hg⟩:=hr
  change MixedCode.evaluationValue L.basis L.matricesK L.unariesK L.weightsK raw=_
  rw [MixedCode.evaluationValue_decode L.basis L.matricesK L.unariesK L.weightsK raw g hd hg.1]
  congr 1
  rw [totalCount_decode q (realRelation L) raw g hd hg.1]
  exact evaluate_eq_count L hunit h01 g hg.1
end PlanarHom.ZeroOneMixedMembership
