import Mathlib.Data.List.NodupEquivFin
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.FinRange
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Exact occurrence indexing for variable replication

A position in `xs.flatMap (fun x => List.replicate (count x) x)` is bijective
with an original list position together with a copy number. The explicit
finite enumeration retains different original occurrences even when their
values coincide, and works when some or all copy counts are zero. The inverse
uses the verified list `idxOf` construction, not a chosen cardinality bijection.
-/

namespace PlanarHom.ReplicationIndex

/-- Enumerate occurrence labels in the same block order as `flatMap replicate`. -/
def copies {m : ℕ} (count : Fin m → ℕ) : List (Σ i : Fin m, Fin (count i)) :=
  (List.finRange m).sigma (fun i => List.finRange (count i))

theorem copies_nodup {m : ℕ} (count : Fin m → ℕ) : (copies count).Nodup :=
  (List.nodup_finRange _).sigma (fun _ => List.nodup_finRange _)

theorem mem_copies {m : ℕ} (count : Fin m → ℕ) (p : Σ i : Fin m, Fin (count i)) :
    p ∈ copies count := by
  rcases p with ⟨i,j⟩
  simp [copies, List.mem_sigma]

theorem map_copies {α : Type*} {m : ℕ} (count : Fin m → ℕ) (value : Fin m → α) :
    (copies count).map (fun p => value p.1) =
      (List.finRange m).flatMap (fun i => List.replicate (count i) (value i)) := by
  simp [copies, List.sigma, List.map_flatMap, List.map_map, Function.comp_def]

theorem map_copies_get {α : Type*} (xs : List α) (count : α → ℕ) :
    (copies (fun i => count (xs.get i))).map (fun p => xs.get p.1) =
      xs.flatMap (fun x => List.replicate (count x) x) := by
  rw [map_copies]
  have hx : (List.finRange xs.length).map xs.get = xs := by
    rw [← List.ofFn_eq_map, List.ofFn_get]
  calc
    _ = ((List.finRange xs.length).map xs.get).flatMap
        (fun x => List.replicate (count x) x) := by rw [List.flatMap_map]
    _ = _ := by rw [hx]

theorem copies_length {α : Type*} (xs : List α) (count : α → ℕ) :
    (copies (fun i => count (xs.get i))).length =
      (xs.flatMap (fun x => List.replicate (count x) x)).length := by
  simpa using congrArg List.length (map_copies_get xs count)

/-- The exact list-index/occurrence-and-copy bijection. -/
def replicateEquiv {α : Type*} (xs : List α) (count : α → ℕ) :
    Fin (xs.flatMap (fun x => List.replicate (count x) x)).length ≃
      Σ i : Fin xs.length, Fin (count (xs.get i)) :=
  (finCongr (copies_length xs count).symm).trans
    ((copies_nodup _).getEquivOfForallMemList _ (mem_copies _))

/-- The bijection preserves the exact original occurrence value, hence any
endpoint or label projection of that value. -/
theorem get_replicateEquiv {α : Type*} (xs : List α) (count : α → ℕ)
    (j : Fin (xs.flatMap (fun x => List.replicate (count x) x)).length) :
    (xs.flatMap (fun x => List.replicate (count x) x)).get j =
      xs.get (replicateEquiv xs count j).1 := by
  have hi : j.val < (copies (fun i => count (xs.get i))).length := by
    rw [copies_length]
    exact j.isLt
  have hget := congrArg (fun l : List α => l[j.val]?) (map_copies_get xs count)
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
    List.getElem?_eq_getElem j.isLt, Option.map_some] at hget
  exact (Option.some.inj hget).symm

end PlanarHom.ReplicationIndex
