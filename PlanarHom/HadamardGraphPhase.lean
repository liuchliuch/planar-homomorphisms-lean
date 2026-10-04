import PlanarHom.BooleanQuadraticCorrectness
import PlanarHom.BooleanTensorFPSemantics

/-! NEW source semantics: every original labelled edge occurrence contributes
its exact Boolean quadratic monomial. Loops and parallel edges are retained. -/
namespace PlanarHom.BooleanQuadratic
open Complexity
open scoped BigOperators

 theorem bit_fold_xor (xs : List Bool) (z : Bool) :
    bit (xs.foldl xor z)=bit z+(xs.map bit).sum := by
  induction xs generalizing z with
  | nil=>simp
  | cons a xs ih=>simp [ih,add_assoc]
 theorem bit_xorList (xs : List Bool) : bit (xorList xs)=(xs.map bit).sum := by
  simpa [xorList] using bit_fold_xor xs false

 theorem sum_map_edges {g : MixedCode} (f : ℕ×ℕ×ℕ→F₂) :
    (g.edges.map f).sum=∑e:Fin g.edges.length,f (g.edges.get e) := by
  rw [←List.ofFn_getElem_eq_map,List.sum_ofFn]
  rfl

 theorem bit_entry_ofGraph (g : MixedCode) (i j : Fin g.vertices) :
    bit (entry (ofGraph g) i.val j.val)=
      ∑e:Fin g.edges.length,bit (((g.edges.get e).1==i.val) && ((g.edges.get e).2.1==j.val)) := by
  simp only [entry,ofGraph]
  simp only [List.getElem?_map,List.getElem?_range,i.isLt,j.isLt,ite_true,Option.map_some,Option.getD_some]
  rw [bit_xorList]
  simp only [List.map_map,Function.comp_def]
  exact sum_map_edges _

 theorem phase_ofGraph (g : MixedCode) (hg : g.Valid 1 0) (x : Fin g.vertices→F₂) :
    phase g.vertices (ofGraph g) x=
      ∑e:Fin g.edges.length,x ((g.toMultiGraph hg).src e)*x ((g.toMultiGraph hg).dst e) := by
  classical
  unfold phase form
  have hl (i:Fin g.vertices) : bit (rawLinear (ofGraph g) i.val)=0 := by
    simp [rawLinear,ofGraph]
  simp only [hl,zero_mul,Finset.sum_const_zero,add_zero]
  change (0:F₂)+(∑i:Fin g.vertices,∑j:Fin g.vertices,
    bit (entry (ofGraph g) i.val j.val)*x i*x j)=_
  rw [zero_add]
  simp_rw [bit_entry_ofGraph,Finset.sum_mul]
  conv_lhs => arg 2; ext i; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  let s:Fin g.vertices:=(g.toMultiGraph hg).src e
  let d:Fin g.vertices:=(g.toMultiGraph hg).dst e
  have hbit (i j:Fin g.vertices) :
      bit (((g.edges.get e).1==i.val) && ((g.edges.get e).2.1==j.val))=
        if s=i ∧ d=j then 1 else 0 := by
    change bit ((s.val==i.val) && (d.val==j.val))=_
    rw [fin_beq_val,fin_beq_val]
    by_cases hs:s=i <;> by_cases hd:d=j <;> simp [hs,hd,bit]
  simp only [hbit,ite_mul,one_mul,zero_mul]
  simp [ite_and,s,d]

 theorem character_sum {K : Type*} [CommRing K] {E : Type*} (s : Finset E) (f : E→F₂) :
    character (K:=K) (∑e∈s,f e)=∏e∈s,character (f e) := by
  classical
  induction s using Finset.induction_on with
  | empty=>simp
  | @insert e s he ih=>simp [he,character_add,ih]

 def hadamard {K : Type*} [CommRing K] : Matrix Bool Bool K :=
  fun i j=>if i && j then -1 else 1

 theorem hadamard_entry {K : Type*} [CommRing K] (i j : Bool) :
    hadamard (K:=K) i j=character (bit i*bit j) := by
  rw [←bit_and,character_bit]
  rfl

 theorem gauss_ofGraph {K : Type} [CommRing K] (g : MixedCode) (hg : g.Valid 1 0) :
    gauss (K:=K) g.vertices (ofGraph g)=
      g.evaluate (C:=Bool) (R:=K) hg (fun _:Fin 1=>hadamard (K:=K)) BooleanTensorFPClosure.emptyUnaries (fun _=>1) := by
  classical
  rw [BooleanTensorFPClosure.evaluate_unweighted,MultiGraph.unweighted_eq]
  unfold gauss
  let e : (Fin g.vertices→Bool)≃(Fin g.vertices→F₂):=Equiv.piCongrRight (fun _=>bitEquiv)
  rw [←e.sum_comp]
  apply Finset.sum_congr
  · ext x; simp
  intro x hx
  rw [phase_ofGraph g hg,character_sum]
  apply Finset.prod_congr rfl
  intro a ha
  exact (hadamard_entry (x ((g.toMultiGraph hg).src a)) (x ((g.toMultiGraph hg).dst a))).symm

end PlanarHom.BooleanQuadratic
