import PlanarHom.SignedNandIdempotence
import PlanarHom.RoutingIncidencePlanarity
import Mathlib.Algebra.BigOperators.Fin

/-! Exact signed semantics of the fully serialized numeric graph, including
all retained isolated Boolean vertices, empty formulas and repeated literals. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.SignedNandNumeric
open Complexity ParsimoniousNorOneInThree SignedNandExactOneClause

def matrices : Fin 1 → Matrix Bool Bool ℚ := fun _ => nandWeight

def unaries : Fin 1 → Bool → ℚ := fun _ => centerActivity

def readColor {n : ℕ} (σ : Fin n → Bool) (i : ℕ) : Bool := if h : i<n then σ ⟨i,h⟩ else false

@[simp] theorem readColor_fin {n : ℕ} (σ : Fin n → Bool) (i : Fin n) : readColor σ i.val=σ i := by
  simp [readColor,i.isLt]

def colorEquiv (f : NumericFormula) :
    (Fin (compile f).vertices → Bool) ≃ ((Fin f.1 ⊕ Fin f.2.length) → Bool) :=
  Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)

@[simp] theorem colorEquiv_old (f : NumericFormula) (σ : Fin (compile f).vertices → Bool) (i : Fin f.1) :
    colorEquiv f σ (.inl i)=readColor σ i.val := by
  change σ (finSumFinEquiv (.inl i))=readColor σ i.val
  exact (readColor_fin σ (finSumFinEquiv (.inl i))).symm

@[simp] theorem colorEquiv_center (f : NumericFormula) (σ : Fin (compile f).vertices → Bool) (i : Fin f.2.length) :
    colorEquiv f σ (.inr i)=readColor σ (f.1+i.val) := by
  change σ (finSumFinEquiv (.inr i))=readColor σ (f.1+i.val)
  exact (readColor_fin σ (finSumFinEquiv (.inr i))).symm

theorem list_zipIdx_ofFn {A : Type} (xs : List A) :
    xs.zipIdx=List.ofFn (fun i : Fin xs.length => (xs.get i,i.val)) := by
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_zipIdx,List.getElem_ofFn,List.get_eq_getElem,Nat.zero_add]

theorem list_range_ofFn (n : ℕ) : List.range n=List.ofFn (fun i : Fin n => i.val) := by
  apply List.ext_getElem <;> simp

theorem prod_flatMap_map {A B R : Type} [Monoid R] (xs : List A) (f : A → List B) (w : B → R) :
    ((xs.flatMap f).map w).prod=(xs.map (fun a => ((f a).map w).prod)).prod := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.flatMap_cons,List.map_append,List.prod_append,List.map_cons,List.prod_cons,ih]

abbrev formulaPort (f : NumericFormula) (hf : NumericValid f) := NumericFormulaIncidence.clauseVariable f hf

theorem clause_edge_product (f : NumericFormula) (hf : NumericValid f)
    (σ : Fin (compile f).vertices → Bool) (c : Fin f.2.length) :
    ((clauseEdges f.1 (f.2.get c,c.val)).map (edgeWeight (readColor σ))).prod=
      ∏ j : Fin 6,nandWeight
        (colorEquiv f σ ((SignedNandFormulaIdentity.graph (formulaPort f hf)).src (c,j)))
        (colorEquiv f σ ((SignedNandFormulaIdentity.graph (formulaPort f hf)).dst (c,j))) := by
  simp only [Fin.prod_univ_succ,SignedNandFormulaIdentity.graph,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,Matrix.tail_cons,colorEquiv_old,colorEquiv_center]
  simp [clauseEdges,edgeWeight,formulaPort,NumericFormulaIncidence.clauseVariable,
    NumericFormulaIncidence.coordinate,List.prod_cons]

theorem raw_product_eq (f : NumericFormula) (hf : NumericValid f)
    (σ : Fin (compile f).vertices → Bool) :
    ((rawEdges f).map (edgeWeight (readColor σ))).prod=
      ∏ e : Fin f.2.length × Fin 6,nandWeight
        (colorEquiv f σ ((SignedNandFormulaIdentity.graph (formulaPort f hf)).src e))
        (colorEquiv f σ ((SignedNandFormulaIdentity.graph (formulaPort f hf)).dst e)) := by
  rw [Fintype.prod_prod_type]
  unfold rawEdges
  rw [prod_flatMap_map,list_zipIdx_ofFn,List.map_ofFn,List.prod_ofFn]
  exact Finset.prod_congr rfl (fun c _ => clause_edge_product f hf σ c)

theorem binary_product_eq (f : NumericFormula) (hf : NumericValid f)
    (σ : Fin (compile f).vertices → Bool) :
    ((compile f).edges.map (MixedCode.binaryValue (compile f).vertices 1 matrices σ)).prod=
      ((rawEdges f).map (edgeWeight (readColor σ))).prod := by
  rw [←edge_product_eq_raw]
  apply congrArg List.prod
  change ((edges f).map (fun e => (e.1,e.2,0))).map _=_
  rw [List.map_map]
  apply List.map_congr_left
  intro e he
  have hv := (compile_valid f hf).1 (e.1,e.2,0) (List.mem_map.mpr ⟨e,he,rfl⟩)
  simp only [Function.comp_apply,MixedCode.binaryValue,dif_pos hv,matrices,edgeWeight,readColor,
    dif_pos hv.1,dif_pos hv.2.1]

theorem unary_product_eq (f : NumericFormula) (σ : Fin (compile f).vertices → Bool) :
    ((compile f).unaries.map (MixedCode.unaryValue (compile f).vertices 1 unaries σ)).prod=
      ∏ c : Fin f.2.length,centerActivity (colorEquiv f σ (.inr c)) := by
  change (((List.range f.2.length).map (fun i => (f.1+i,0))).map _).prod=_
  rw [List.map_map,list_range_ofFn,List.map_ofFn,List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  have hi : f.1+i.val<(compile f).vertices ∧ 0<1 := by change f.1+i.val<f.1+f.2.length ∧ _; omega
  simp only [Function.comp_apply,MixedCode.unaryValue,dif_pos hi,unaries,colorEquiv_center,
    readColor,dif_pos hi.1]

/-- The mixed-code assignment weight is exactly the literal graph weight;
deduplication changes no NAND product and every marked center remains. -/
theorem evaluate_eq_partition (f : NumericFormula) (hf : NumericValid f) :
    (compile f).evaluate (compile_valid f hf) matrices unaries (fun _ => 1)=
      SignedNandFormulaIdentity.partition (R:=ℚ) (formulaPort f hf) := by
  classical
  letI : DecidableEq (Fin f.1) := fun a b => Classical.propDecidable (a=b)
  letI : DecidableEq (Fin f.2.length) := fun a b => Classical.propDecidable (a=b)
  unfold MixedCode.evaluate SignedNandFormulaIdentity.partition
  apply Fintype.sum_equiv (colorEquiv f)
  intro σ
  simp only [Finset.prod_const_one,one_mul,binary_product_eq f hf σ,raw_product_eq f hf σ,
    unary_product_eq,SignedNandFormulaIdentity.weight]

/-- The finite formula predicate is literally the list-based source predicate. -/
theorem formula_satisfies_iff (f : NumericFormula) (hf : NumericValid f) (b : Fin f.1 → Bool) :
    SignedNandFormulaIdentity.Satisfies (formulaPort f hf) b ↔
      Satisfies f.2 (CountingCookLevin.readBit (List.ofFn b)) := by
  constructor
  · intro h c hc
    obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hc
    have hh := h i
    have hv := hf (f.2.get i) (List.get_mem _ _)
    simp only [List.get_eq_getElem] at hv
    simpa [formulaPort,NumericFormulaIncidence.clauseVariable,NumericFormulaIncidence.coordinate,
      CountingCookLevin.readBit,List.getElem?_ofFn,hv.1,hv.2.1,hv.2.2] using hh
  · intro h c
    have hh := h (f.2.get c) (List.get_mem _ _)
    have hv := hf (f.2.get c) (List.get_mem _ _)
    simp only [List.get_eq_getElem] at hv
    simpa [formulaPort,NumericFormulaIncidence.clauseVariable,NumericFormulaIncidence.coordinate,
      CountingCookLevin.readBit,List.getElem?_ofFn,hv.1,hv.2.1,hv.2.2] using hh

theorem formula_count_eq (f : NumericFormula) (hf : NumericValid f) :
    SignedNandFormulaIdentity.count (formulaPort f hf)=CountingPositiveOneInThree.count f := by
  classical
  unfold SignedNandFormulaIdentity.count CountingPositiveOneInThree.count
  rw [Fintype.card_eq_nat_card,Fintype.card_eq_nat_card]
  exact Nat.card_congr (Equiv.subtypeEquivRight (formula_satisfies_iff f hf))

/-- Exact signed partition, with no multiplicity factor or interpolation. -/
theorem evaluate_eq_count (f : NumericFormula) (hf : NumericValid f) :
    (compile f).evaluate (compile_valid f hf) matrices unaries (fun _ => 1)=
      (CountingPositiveOneInThree.count f : ℚ) := by
  rw [evaluate_eq_partition f hf,SignedNandFormulaIdentity.partition_eq_count,formula_count_eq f hf]

end PlanarHom.SignedNandNumeric
