import PlanarHom.BooleanRetentionPrograms
import PlanarHom.BooleanInnerRecoveryCorrectness
import PlanarHom.BooleanAnswerSlices

/-! NEW correctness of the emitted path-power queries and their actual answer
blocks. Ordinary planar promises allow loops and duplicate occurrences. -/
noncomputable section
set_option maxHeartbeats 1000000
open Classical
namespace PlanarHom.BooleanRetentionQuerySemantics
open Complexity Complexity.MixedCode BooleanRetentionPrograms BooleanTensorPartitionMoments
open BooleanInnerRecoveryCorrectness BooleanSpectralCounts
variable {K : Type} [Field K] [Algebra ℚ K] [DecidableEq K] {b d bt ut : ℕ}

theorem queryAt_eq (selected : ℕ) (mult : Fin b→ℕ) (p : Query) (k : ℕ)
    (hk:k<cap selected mult p.2) :
    queryAt selected mult (p,k)=(p.1,p.2.stretchLabel selected selected k) := by
  simp [queryAt,min_eq_right (Nat.le_of_lt hk)]

@[simp] theorem innerQueries_length (selected : ℕ) (mult : Fin b→ℕ) (p : Query) :
    (innerQueries selected mult p).length=cap selected mult p.2 := by
  simp [innerQueries]

theorem query_mem (selected : ℕ) (mult : Fin b→ℕ) (p z : Query)
    (hz:z∈innerQueries selected mult p) :
    ∃k,k<cap selected mult p.2 ∧ z=(p.1,p.2.stretchLabel selected selected k) := by
  obtain ⟨k,hk,rfl⟩:=List.mem_map.mp hz
  exact ⟨k,List.mem_range.mp hk,queryAt_eq selected mult p k (List.mem_range.mp hk)⟩

theorem prepare_queries_planar (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b)
    (selected : Fin bt) (g : MixedCode) (hg:g.PlanarValid bt ut) (z : Query)
    (hz:z∈(prepare selected.val c a w (multiplicity cls) g0 g).2) :
    z.1∈BooleanEffectiveLengthSamples.samples c a w (multiplicity cls) (multiplicity cls g0)
      (g.markedCount selected.val) ∧ z.2.PlanarValid bt ut := by
  obtain ⟨q,hq,hz⟩:=List.mem_flatMap.mp hz
  obtain ⟨k,_,rfl⟩:=query_mem selected.val (multiplicity cls) (q,g) z hz
  exact ⟨hq,g.stretchLabel_planar hg selected.val selected.val k selected.isLt
    (fun e he _=>(hg.1.1 e he).2.2)⟩

def sourceAnswer (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (p : Query) : K :=
  totalEvaluation (replace M selected (sourceMatrix cls c a w p.1)) U (fun _=>1) p.2

theorem sourceAnswer_query (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (q : ℚ) (k : ℕ) :
    sourceAnswer selected M U cls c a w (q,g.stretchLabel selected.val selected.val k)=
      g.evaluate hg (replace M selected ((sourceMatrix cls c a w q)^(k+1))) U (fun _=>1) := by
  rw [sourceAnswer,totalEvaluation_valid _ _ _ _
    (g.stretchLabel_valid hg selected.val selected.val k selected.isLt (fun e he _=>(hg.1 e he).2.2)),
    g.evaluate_stretchLabel hg selected.val k selected (fun e he _=>(hg.1 e he).2.2)]
  congr 1
  funext l
  by_cases hl:l=selected
  · subst l
    simp [pathPowerLabels,replace]
  · have hv:l.val≠selected.val:=fun h=>hl (Fin.ext h)
    simp [pathPowerLabels,replace,hl,hv,l.isLt]

theorem innerAnswers_eq (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (q : ℚ) :
    (innerQueries selected.val (multiplicity cls) (q,g)).map (sourceAnswer selected M U cls c a w)=
      positiveMoments g hg selected M U (fun _=>1) cls c a w q := by
  apply List.ext_getElem
  · simp only [List.length_map,innerQueries,List.length_range,positiveMoments,List.length_ofFn,cap]
  · intro k hk hk'
    have hkc:k<cap selected.val (multiplicity cls) g:=by simpa only [List.length_map,innerQueries,List.length_range] using hk
    simp only [innerQueries,List.getElem_map,List.getElem_range,
      queryAt_eq selected.val (multiplicity cls) (q,g) k hkc,positiveMoments,List.getElem_ofFn]
    exact sourceAnswer_query g hg selected M U cls c a w q k

theorem answerBlock_eq (g : MixedCode) (hg:g.Valid bt ut) (selected : Fin bt)
    (M : Fin bt→Matrix (Fin d→Bool) (Fin d→Bool) K) (U : Fin ut→(Fin d→Bool)→K)
    (cls : Fin d→Fin b) (c a w : Fin b→K) (g0 : Fin b)
    (q : ℚ) (j : ℕ)
    (hj:(q,j)∈(prepare selected.val c a w (multiplicity cls) g0 g).1.2.zipIdx) :
    answerBlock (multiplicity cls)
      (((prepare selected.val c a w (multiplicity cls) g0 g).1,
        (prepare selected.val c a w (multiplicity cls) g0 g).2.map
          (sourceAnswer selected M U cls c a w)),j)=
      positiveMoments g hg selected M U (fun _=>1) cls c a w q := by
  let xs:=BooleanEffectiveLengthSamples.samples c a w (multiplicity cls)
    (multiplicity cls g0) (g.markedCount selected.val)
  have hj':(q,j)∈xs.zipIdx:=hj
  obtain ⟨hlt,hval⟩:=List.mem_zipIdx' hj'
  unfold answerBlock prepare
  simp only [List.map_flatMap]
  rw [BooleanAnswerSlices.slice_flatMap xs
    (fun x=>(innerQueries selected.val (multiplicity cls) (x,g)).map
      (sourceAnswer selected M U cls c a w))
    (BooleanInnerRecoveryProgram.queryCount (multiplicity cls) (g.markedCount selected.val))
    (by intro x _;simp [cap]) j hlt,←hval]
  exact innerAnswers_eq g hg selected M U cls c a w q

end PlanarHom.BooleanRetentionQuerySemantics
