import PlanarHom.MaterializedFormulaRouting
import PlanarHom.CountingPositiveOneInThreeHardness

/-! Complete materialized positive-formula routing compiler and exact count
preservation. Global geometric realization and whole-compiler FP are separate
obligations, not assumptions hidden in this theorem. -/
noncomputable section
open Classical
namespace PlanarHom.PositiveBlockProgram
open ParsimoniousNorOneInThree CountingCookLevin

def formulaLayers (n m : ℕ) (rs : List ℕ) : Formula ℕ → LayerResult
  | [] => .identity m rs
  | c::cs =>
    let first := clauseLayer n m rs c
    first.then (formulaLayers n first.variableCount first.rails cs)

structure LayerResult.Complete (m n : ℕ) (r : LayerResult) : Prop extends r.WellFormed m where
  rails_length : r.rails.length=n

theorem formulaLayers_complete (f : Formula ℕ) (n m : ℕ) (rs : List ℕ)
    (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hf : NumericValid (n,f)) :
    (formulaLayers n m rs f).Complete m n := by
  induction f generalizing m rs with
  | nil => exact ⟨⟨trivial,rfl,hr⟩,hlen⟩
  | cons c cs ih =>
    have hc := hf c (by simp)
    have hcs : NumericValid (n,cs) := fun d hd => hf d (by simp [hd])
    have hfirst := clauseLayer_wellFormed n m rs c hr hlen hc
    have hlen' := clauseLayer_length n m rs c hr hlen hc
    have htail := ih _ _ hfirst.rails_valid hlen' hcs
    exact ⟨hfirst.then htail.toWellFormed,htail.rails_length⟩

/-- No clause termination changes any original rail value. -/
theorem formulaLayers_values (f : Formula ℕ) (n m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hf : NumericValid (n,f)) :
    (formulaLayers n m rs f).rails.map (readBit (execute (formulaLayers n m rs f).instructions xs))=
      rs.map (readBit xs) := by
  induction f generalizing m rs xs with
  | nil => rfl
  | cons c cs ih =>
    have hc := hf c (by simp)
    have hcs : NumericValid (n,cs) := fun d hd => hf d (by simp [hd])
    let first := clauseLayer n m rs c
    let ys := execute first.instructions xs
    have hfirst : first.WellFormed m := clauseLayer_wellFormed n m rs c hr hlen hc
    have hlen' : first.rails.length=n := clauseLayer_length n m rs c hr hlen hc
    have hy : ys.length=first.variableCount := hfirst.store_length xs hxs
    have ht := ih first.variableCount first.rails ys hy hfirst.rails_valid hlen' hcs
    have hv : first.rails.map (readBit ys)=rs.map (readBit xs) := clauseLayer_values n m rs c xs hxs hr hlen hc
    rw [hv] at ht
    change (formulaLayers n first.variableCount first.rails cs).rails.map
      (readBit (execute (first.instructions++(formulaLayers n first.variableCount first.rails cs).instructions) xs))=_
    rw [execute_append]
    exact ht

/-- Acceptance of the literal block program is exactly source satisfaction. -/
theorem formulaLayers_accepts (f : Formula ℕ) (n m : ℕ) (rs : List ℕ) (xs : List Bool)
    (hxs : xs.length=m) (hr : ∀x∈rs,x<m) (hlen : rs.length=n) (hf : NumericValid (n,f)) :
    Accepts (formulaLayers n m rs f).instructions xs ↔ Satisfies f (readBit (rs.map (readBit xs))) := by
  induction f generalizing m rs xs with
  | nil => simp [formulaLayers,LayerResult.identity,Accepts,Satisfies]
  | cons c cs ih =>
    have hc := hf c (by simp)
    have hcs : NumericValid (n,cs) := fun d hd => hf d (by simp [hd])
    let first := clauseLayer n m rs c
    let ys := execute first.instructions xs
    have hfirst : first.WellFormed m := clauseLayer_wellFormed n m rs c hr hlen hc
    have hlen' : first.rails.length=n := clauseLayer_length n m rs c hr hlen hc
    have hy : ys.length=first.variableCount := hfirst.store_length xs hxs
    have ht := ih first.variableCount first.rails ys hy hfirst.rails_valid hlen' hcs
    have hv : first.rails.map (readBit ys)=rs.map (readBit xs) := clauseLayer_values n m rs c xs hxs hr hlen hc
    rw [hv] at ht
    change Accepts (first.instructions++(formulaLayers n first.variableCount first.rails cs).instructions) xs ↔ _
    rw [accepts_append,ht,clauseLayer_accepts n m rs c xs hxs hr hlen hc]
    simp [Satisfies]

end PlanarHom.PositiveBlockProgram

namespace PlanarHom.PositiveRoutingCompiler
open ParsimoniousNorOneInThree CountingCookLevin PositiveBlockProgram

def program (f : NumericFormula) : List Instruction :=
  (formulaLayers f.1 f.1 (List.range f.1) f.2).instructions

def compile (f : NumericFormula) : NumericFormula := PositiveBlockProgram.compile f.1 (program f)

theorem program_valid (f : NumericFormula) (hf : NumericValid f) : Valid f.1 (program f) :=
  (formulaLayers_complete f.2 f.1 f.1 (List.range f.1)
    (fun _ h => List.mem_range.mp h) (by simp) hf).valid

theorem compile_valid (f : NumericFormula) (hf : NumericValid f) : NumericValid (compile f) :=
  network_valid (program f) f.1 (program_valid f hf)

private theorem range_reads (xs : List Bool) : (List.range xs.length).map (readBit xs)=xs := by
  apply NorExactOne.list_eq_of_read
  · simp
  · intro i hi
    have hin : i<xs.length := by simpa using hi
    simp [readBit,List.getElem?_map,hin]

theorem program_accepts (f : NumericFormula) (hf : NumericValid f) (w : Fin f.1 → Bool) :
    Accepts (program f) (List.ofFn w) ↔ Satisfies f.2 (readBit (List.ofFn w)) := by
  have h := formulaLayers_accepts f.2 f.1 f.1 (List.range f.1) (List.ofFn w)
    (by simp) (fun _ hm => List.mem_range.mp hm) (by simp) hf
  have he : (List.range f.1).map (readBit (List.ofFn w))=List.ofFn w := by
    simpa using range_reads (List.ofFn w)
  simpa only [he] using h

/-- Explicit whole compiler bijection, including repeated source variables and
all locally grounded wire/crossover/fanout auxiliaries. -/
def solutionsEquiv (f : NumericFormula) (hf : NumericValid f) :
    NorExactOne.Solutions f ≃ NorExactOne.Solutions (compile f) :=
  (Equiv.subtypeEquivRight (fun w => (program_accepts f hf w).symm)).trans
    (PositiveBlockProgram.solutionsEquiv f.1 (program f) (program_valid f hf))

/-- Exact counts, with no unknown extension multiplicity or correction factor. -/
theorem count_preserved (f : NumericFormula) (hf : NumericValid f) :
    CountingPositiveOneInThree.count (compile f)=CountingPositiveOneInThree.count f :=
  (Fintype.card_congr (solutionsEquiv f hf)).symm

end PlanarHom.PositiveRoutingCompiler
