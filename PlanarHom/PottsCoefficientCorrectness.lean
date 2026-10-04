import PlanarHom.PottsCoefficientPrograms
import PlanarHom.MixedParallelSemantics

/-! The concrete answer list from the emitted ordinary parallel graphs is
exactly the sample table consumed by the actual coefficient machine. -/
noncomputable section
open Classical
namespace PlanarHom.PottsCoefficientPrograms
open Complexity Complexity.MixedCode ProperColoringPottsReduction PottsCentered

def sampleAnswer (q : ℕ) (g : MixedCode) : ℚ :=
  totalEvaluation (fun _ : Fin 1 => positivePottsMatrix q) (noUnaries q) (fun _ => 1) g

def actualAnswers (q : ℕ) (g : MixedCode) : List ℚ := (queries g).map (sampleAnswer q)

theorem sampleAnswer_parallel (q : ℕ) (g : MixedCode) (hg : g.Valid 1 0) (k : ℕ) :
    sampleAnswer q (g.parallelLabel 0 k)=
      (g.toMultiGraph hg).unweighted (fun i j => positivePottsMatrix q i j^k) := by
  rw [sampleAnswer,totalEvaluation_valid _ _ _ _ (parallelLabel_valid 0 k 1 0 g hg),
    evaluate_parallelLabel]
  have hm : (fun (l : Fin 1) i j => if l.val=0 then positivePottsMatrix q i j^k else
      positivePottsMatrix q i j) = fun (_ : Fin 1) i j => positivePottsMatrix q i j^k := by
    funext l i j
    have : l.val=0 := by omega
    simp [this]
  rw [hm]
  simpa only [noUnaries,MultiGraph.unweighted] using
    (evaluate_homogeneous g hg (fun i j => positivePottsMatrix q i j^k) (fun _ => 1))

theorem actualAnswers_getD (q : ℕ) (g : MixedCode) (i : ℕ) (hi : i<g.edges.length+1) :
    (actualAnswers q g).getD i 0=sampleAnswer q (g.parallelLabel 0 (i+1)) := by
  rw [List.getD_eq_getElem _ _ (by simpa [actualAnswers,queries,GraphInterpolationQueries.queries] using hi)]
  simp [actualAnswers,queries,GraphInterpolationQueries.queries]

theorem row_actual (q : ℕ) (hq : 0<q) (d : ℕ) (g : MixedCode) (hg : g.Valid 1 0)
    (i : ℕ) (hi : i<g.edges.length+1) :
    row q ((prepare (d,g)).1,actualAnswers q g) i=
      (sampleNode q (i+1),(polynomial (g.toMultiGraph hg) q).eval (sampleNode q (i+1))) := by
  simp only [row,prepare,min_eq_right (show i+1≤g.edges.length+1 by omega)]
  rw [actualAnswers_getD q g i hi,sampleAnswer_parallel q g hg]
  rw [eval_sample _ q (i+1) hq]
  simp only [Fintype.card_fin]

theorem table_actual (q : ℕ) (hq : 0<q) (d : ℕ) (g : MixedCode) (hg : g.Valid 1 0) :
    table q ((prepare (d,g)).1,actualAnswers q g)=
      (List.range (g.edges.length+1)).map (fun i =>
        (sampleNode q (i+1),(polynomial (g.toMultiGraph hg) q).eval (sampleNode q (i+1)))) := by
  apply List.map_congr_left
  intro i hi
  exact row_actual q hq d g hg i (List.mem_range.mp hi)

/-- Actual ordinary I+J answers recover the requested normalized centered
coefficient, even for loops, parallel occurrences and isolated vertices. -/
theorem coefficient_recovery (q : ℕ) (hq : 0<q) (d : ℕ) (g : MixedCode) (hg : g.Valid 1 0) :
    recover q ((prepare (d,g)).1,(prepare (d,g)).2.map (sampleAnswer q))=coefficientValue q (d,g) := by
  change recover q ((prepare (d,g)).1,actualAnswers q g)=_
  rw [recover,table_actual q hq d g hg]
  have hn : Function.Injective (fun i : ℕ => sampleNode q (i+1)) :=
    (sampleNode_injective q hq).comp (fun _ _ h => Nat.succ.inj h)
  have hlen : (polynomial (g.toMultiGraph hg) q).degree<↑(g.edges.length+1) := by
    apply lt_of_le_of_lt Polynomial.degree_le_natDegree
    have hd := natDegree_le (g.toMultiGraph hg) q
    have hd' : (polynomial (g.toMultiGraph hg) q).natDegree<g.edges.length+1 := by
      simpa only [Fintype.card_fin] using Nat.lt_succ_of_le hd
    exact_mod_cast hd'
  have hh := MaterializedPolynomialCoefficientMachines.recover_eq_coeff d
    ((List.range (g.edges.length+1)).map (fun i =>
      (sampleNode q (i+1),(polynomial (g.toMultiGraph hg) q).eval (sampleNode q (i+1)))))
    (by simpa only [List.map_map,Function.comp_def] using List.nodup_range.map hn)
    (polynomial (g.toMultiGraph hg) q) (by simpa using hlen) (by
      intro r hr
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hr
      rfl)
  simpa [coefficientValue,hg,prepare] using hh
end PlanarHom.PottsCoefficientPrograms
