import PlanarHom.ZeroOneSourceStructure
import PlanarHom.TargetGraphDichotomyMachines
import PlanarHom.ZeroOneMixedMembership

/-! NEW exact Theorem 7.1 assembly from the actual source-structure necessity,
unrestricted basic-block machines, and genuine accepting-path membership. The
all-q Potts foundation is explicit only in these reusable internal lemmas. -/
noncomputable section
open Classical
namespace PlanarHom.AlgebraicProductInterpolation.RealLanguage
open Complexity Complexity.MixedCode RootedRestriction ZeroOneBasicStructure
open ZeroOneBasicTractability
variable {q:ℕ}

def BasicZeroOneSupport (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) : Prop :=
  ∀c:(colorSupport (L.matrices 0) hs).ConnectedComponent,
    BasicZeroOneComponent (fun i j:c.supp=>L.matrices 0 i.val j.val)

theorem zeroOne_symmetryK (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) :
    ∀i j,L.matricesK 0 i j=L.matricesK 0 j i := by
  intro i j
  exact Subtype.ext (hs i j)

theorem zeroOne_supportK_eq (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) :
    colorSupport (L.matricesK 0) (zeroOne_symmetryK L hs)=colorSupport (L.matrices 0) hs := by
  ext i j
  change (i≠j ∧ L.matricesK 0 i j≠0) ↔ (i≠j ∧ L.matrices 0 i j≠0)
  have hz:L.matricesK 0 i j=0 ↔ L.matrices 0 i j=0 :=
    ⟨fun h=>congrArg L.field.val h,fun h=>Subtype.ext h⟩
  simp only [ne_eq,hz]

theorem zeroOne_basic_field (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) (h:L.BasicZeroOneSupport hs) :
    ∀c:(colorSupport (L.matricesK 0) (zeroOne_symmetryK L hs)).ConnectedComponent,
      FieldBasicZeroOneComponent (fun i j:c.supp=>L.matricesK 0 i.val j.val) := by
  rw [zeroOne_supportK_eq L hs]
  intro c
  rcases h c with ⟨hne,hone⟩|⟨side,hsurj,hside⟩|⟨hne,hsub,hzero⟩
  · exact Or.inl ⟨hne,fun i j=>Subtype.ext (hone i j)⟩
  · refine Or.inr (Or.inl ⟨side,hsurj,?_⟩)
    intro i j
    apply Subtype.ext
    simpa only [apply_ite,map_zero,map_one] using hside i j
  · refine Or.inr (Or.inr ⟨hne,hsub,?_⟩)
    funext i j
    apply Subtype.ext
    exact congrFun (congrFun hzero i) j

theorem zeroOne_basic_inFP (L:RealLanguage q 1 0)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i) (h:L.BasicZeroOneSupport hs) : L.problem.InFP := by
  apply (evaluation_inFP_iff L.basis L.matricesK L.unariesK L.weightsK).mpr
  have ht:=TargetGraphDichotomy.support_valid_fp L.basis (L.matricesK 0) (zeroOne_symmetryK L hs)
    L.weightsK (zeroOne_basic_field L hs h)
  have hplan:=ht.transportInput (ea:=encoding.restrict (PlanarValid 1 0))
    (fun g:{g:MixedCode // g.PlanarValid 1 0}=>⟨g.val,g.property.1⟩) (fun _=>rfl)
  apply hplan.congr
  intro g
  change g.val.evaluate g.property.1 (fun _:Fin 1=>L.matricesK 0) TargetGraphDichotomy.emptyUnaries L.weightsK=
    g.val.evaluate g.property.1 L.matricesK L.unariesK L.weightsK
  have hm:(fun _:Fin 1=>L.matricesK 0)=L.matricesK := by
    funext l i j
    have hl:l=0:=Subsingleton.elim _ _
    subst l
    rfl
  have hu:TargetGraphDichotomy.emptyUnaries=L.unariesK := by
    funext u
    exact u.elim0
  rw [hm,hu]

theorem theorem71_weighted_of_potts (hPotts:PositivePottsFoundation)
    (L:RealLanguage q 1 0) (hw:∀i,0<L.weights i)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    (L.BasicZeroOneSupport hs → L.problem.InFP) ∧
      (¬L.BasicZeroOneSupport hs → PromisedSharpPHard L.problem) := by
  refine ⟨zeroOne_basic_inFP L hs,?_⟩
  intro hbad
  by_contra hn
  exact hbad (zeroOne_basic_of_not_hard hPotts L hs hw h01 hn)

theorem theorem71_unweighted_of_potts (hPotts:PositivePottsFoundation)
    (L:RealLanguage q 1 0) (hunit:∀i,L.weights i=1)
    (hs:∀i j,L.matrices 0 i j=L.matrices 0 j i)
    (h01:∀i j,L.matrices 0 i j=0 ∨ L.matrices 0 i j=1) :
    (L.BasicZeroOneSupport hs → L.problem.InFP) ∧
      (¬L.BasicZeroOneSupport hs → PromisedSharpPHard L.problem) ∧
      ∃f:Bits→ℕ,SharpP f ∧ ∀raw,L.problem.valid raw →
        L.problem.value raw=(numberFieldEncoding L.basis).encode (f raw:L.field) := by
  have h:=theorem71_weighted_of_potts hPotts L (fun i=>by rw [hunit i]; norm_num) hs h01
  exact ⟨h.1,h.2,ZeroOneMixedMembership.membership L hunit h01⟩
end PlanarHom.AlgebraicProductInterpolation.RealLanguage
