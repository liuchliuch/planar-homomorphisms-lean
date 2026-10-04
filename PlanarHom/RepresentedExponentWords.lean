import PlanarHom.ExponentProductTableMachines
import PlanarHom.BoundedUnaryMachines
import PlanarHom.UnaryRangeMachines
import PlanarHom.ListMutationMachines

/-! Actual bounded canonical alphabet words for exponent vectors. The cap is
unary and the alphabet dimension is fixed, so binary exponents cannot hide an
exponential output. This is independent of any field presentation. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.RepresentedExponentWords
open Complexity PairProjectionMachines

 def inputEncoding (t:ℕ) : BitEncoding (ℕ×(Fin t→ℕ)) :=
  BitEncoding.unaryNat.prod (BitEncoding.nat.vector t)

def word {t:ℕ} (m:ℕ) (r:Fin t→ℕ) : List ℕ :=
  (List.finRange t).flatMap (fun i=>List.replicate (min m (r i)) i.val)

theorem fp_replicate (i:ℕ) : FP BitEncoding.unaryNat BitEncoding.nat.list (fun n=>List.replicate n i) := by
  have h:=UnaryRangeMachines.fp_range.comp
    (ListMapMachines.fp_map BitEncoding.nat BitEncoding.nat (fun _=>i) (fp_const _ _ i))
  apply h.congr
  intro n
  simp

theorem fp_flatMap_fixed {A I B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (is:List I) (f:I→A→List B) (hf:∀i∈is,FP ea eb.list (f i)) :
    FP ea eb.list (fun a=>is.flatMap (fun i=>f i a)) := by
  induction is with
  | nil=>exact fp_const _ _ []
  | cons i is ih=>
    exact (((hf i (List.mem_cons_self)).pair
      (ih (fun j hj=>hf j (List.mem_cons_of_mem _ hj)))).comp (ListMutationMachines.fp_append eb))

theorem fp_word (t:ℕ) : FP (inputEncoding t) BitEncoding.nat.list (fun p=>word p.1 p.2) := by
  apply fp_flatMap_fixed (inputEncoding t) BitEncoding.nat (List.finRange t)
  intro i hi
  have hm:=fp_fst BitEncoding.unaryNat (BitEncoding.nat.vector t)
  have hr:=(fp_snd BitEncoding.unaryNat (BitEncoding.nat.vector t)).comp
    (FixedVectorMachines.fp_coordinate BitEncoding.nat t i)
  exact ((hm.pair hr).comp ⟨BoundedUnaryMachines.computer⟩).comp (fp_replicate i.val)

theorem mem_word_bound {t m:ℕ} {r:Fin t→ℕ} {i:ℕ} (hi:i∈word m r) : i<t := by
  obtain ⟨j,hj,hi⟩:=List.mem_flatMap.mp hi
  have he:i=j.val:=List.eq_of_mem_replicate hi
  simpa only [he] using j.isLt

theorem length_word {t:ℕ} (m:ℕ) (r:Fin t→ℕ) :
    (word m r).length=∑i,min m (r i) := by
  simp [word,List.finRange,List.length_flatMap,List.sum_ofFn]

theorem length_word_le {t:ℕ} (m:ℕ) (r:Fin t→ℕ) : (word m r).length≤t*m := by
  rw [length_word]
  calc
    _≤∑_:Fin t,m:=Finset.sum_le_sum (fun i hi=>Nat.min_le_left _ _)
    _=t*m:=by simp

def symbol {K:Type} [One K] {t:ℕ} (A:Fin t→K) (i:ℕ) : K := if hi:i<t then A ⟨i,hi⟩ else 1

theorem word_product {K:Type} [CommMonoid K] {t:ℕ} (A:Fin t→K) (m:ℕ) (r:Fin t→ℕ) :
    ((word m r).map (symbol A)).prod=∏i,A i^(min m (r i)) := by
  simp [word,List.map_flatMap,List.flatMap_def,List.prod_flatten,symbol,List.finRange,List.prod_ofFn,List.map_map,Function.comp_def]

theorem word_product_of_vector {K:Type} [CommMonoid K] {t m:ℕ} (A:Fin t→K)
    {r:Fin t→ℕ} (hr:r∈ExponentProductTables.vectors t m) :
    ((word m r).map (symbol A)).prod=∏i,A i^(r i) := by
  rw [word_product]
  apply Finset.prod_congr rfl
  intro i hi
  rw [min_eq_right (ExponentProductTables.coordinate_le hr i)]

end PlanarHom.RepresentedExponentWords
