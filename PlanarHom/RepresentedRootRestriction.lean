import PlanarHom.RepresentedPresentationPipeline
import PlanarHom.RepresentedFixedLinearArithmetic
import PlanarHom.RootedHomogeneousSemantics
import PlanarHom.RootedConditionalSemantics
import PlanarHom.RootedQueryMachines

/-! The actual homogeneous root-restriction reduction over any honestly
presented ordered field with represented addition and multiplication. Fixed
projection coefficients are hard-coded source data. No finite Q-basis, field
order algorithm, preferred representative, or uncharged oracle is assumed. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedRootRestriction
open Complexity Complexity.MixedCode RepresentedBit
variable {K C:Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [Fintype C]

def inputValid (p:ℕ×MixedCode) : Prop := p.2.PlanarValid 1 0 ∧ p.1<p.2.vertices

def rootValue (M:Matrix C C K) (w:C→K) (X:Set C) (p:ℕ×MixedCode) : K :=
  if hg:p.2.Valid 1 0 then
    if hr:p.1<p.2.vertices then (p.2.toMultiGraph hg).rootRestricted ⟨p.1,hr⟩ M w X else 0
  else 0

def rootProblem (P:Presentation K) (M:Matrix C C K) (w:C→K) (X:Set C) : Problem :=
  P.problem RootedCodeMachines.inputEncoding inputValid (rootValue M w X)

def sourceProblem (P:Presentation K) (M:Matrix C C K) (w:C→K) : Problem :=
  P.problem MixedCode.encoding (PlanarValid 1 0)
    (totalEvaluation (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w)

private theorem exists_ofFn {B:Type} {k:ℕ} (bs:List B) (h:bs.length=k) :
    ∃y:Fin k→B,bs=List.ofFn y := by
  subst k
  exact ⟨bs.get,(List.ofFn_get bs).symm⟩

def rootReduction (P:Presentation K) (ops:AddMulMachines P)
    (M:Matrix C C K) (w:C→K) (hw:∀i,0 < w i) (X:Set C) :
    Reduction (rootProblem P M w X) (sourceProblem P M w) := by
  let data:=RootedRestriction.exists_computed_root_queries M w hw X
  let k:=Classical.choose data
  let graphs:=Classical.choose (Classical.choose_spec data)
  let c:=Classical.choose (Classical.choose_spec (Classical.choose_spec data))
  have hcorrect:=Classical.choose_spec (Classical.choose_spec (Classical.choose_spec data))
  let coeff:Fin k→P.Code:=fun r=>P.constant (c r)
  let recover:ℕ×List P.Code→P.Code:=fun p=>ops.dot k coeff p.2
  have hr:FP (BitEncoding.nat.prod P.encoding.list) P.encoding recover:=
    (PairProjectionMachines.fp_snd BitEncoding.nat P.encoding.list).comp (ops.fp_dot k coeff)
  apply presentationPipeline P P RootedCodeMachines.inputEncoding BitEncoding.nat MixedCode.encoding
    (BitEncoding.prodNormalizer BitEncoding.natNormalizer MixedCode.normalizer) BitEncoding.natNormalizer
    inputValid (PlanarValid 1 0) (rootValue M w X)
    (totalEvaluation (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w)
    (RootedRestriction.prepare graphs) recover (RootedRestriction.fp_prepare graphs) hr
  · intro p hp query hq
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp hq
    exact RootedCodeMachines.attach_planarValid (graphs j).2.2.val (graphs j).2.2.property 0
      p.2 hp.1 ⟨p.1,hp.2⟩ (by decide)
  · intro p hp bs hbs
    have hlen:bs.length=k := by
      have hh:=hbs.length_eq
      simpa only [RootedRestriction.prepare,List.length_ofFn] using hh.symm
    obtain ⟨ys,rfl⟩:=exists_ofFn bs hlen
    have hy:∀j,P.valid (ys j) ∧ P.value (ys j)=
        totalEvaluation (fun _:Fin 1=>M) (fun i:Fin 0=>i.elim0) w
          (RootedCodeMachines.attach (graphs j).2.2.val 0 p) := by
      intro j
      have h:=(List.forall₂_iff_get.mp hbs).2 j.val
        (by simpa only [RootedRestriction.prepare,List.length_ofFn] using j.isLt)
        (by simpa only [List.length_ofFn] using j.isLt)
      simpa only [RootedRestriction.prepare,List.get_ofFn] using h
    have hd:=ops.dot_ofFn k coeff ys (fun r=>P.constant_valid (c r)) (fun r=>(hy r).1)
    refine ⟨hd.1,?_⟩
    change P.value (ops.dot k coeff (List.ofFn ys))=rootValue M w X p
    rw [hd.2]
    have he:=hcorrect p.2 hp.1 ⟨p.1,hp.2⟩
    rw [MultiGraph.atRoot_restricted] at he
    simp only [rootValue,dif_pos hp.1.1,dif_pos hp.2]
    rw [he]
    apply Finset.sum_congr rfl
    intro j hj
    simp only [coeff,Presentation.constant_value,(hy j).2]
    rfl

end PlanarHom.RepresentedRootRestriction
