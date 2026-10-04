import PlanarHom.PowerRootCoordinateCandidates
import PlanarHom.ListDropMachines
import PlanarHom.ListContextFilterMachines
import PlanarHom.FixedFieldPolynomialMachines

/-! # Actual enumeration and verification of all fixed-field power roots

All candidate coordinate tuples are assembled by fixed finite circuits, then
the exact power equation is tested by actual field machines. The resulting
list contains every root in the fixed field and contains no nonroot.
-/

noncomputable section
namespace PlanarHom.FixedFieldPowerRootCandidates
open Complexity ArithmeticCircuitPrimitives PairProjectionMachines

variable {K : Type} [Field K] [Algebra ℚ K] [FiniteDimensional ℚ K]
variable {d : ℕ} (basis : Module.Basis (Fin d) ℚ K)
local instance : DecidableEq K := Classical.decEq K

def coordinateBound (n d : ℕ) : ℕ := 3^((n*d)^d)*(n*d)^d

def choices (n d : ℕ) : List (Fin d → Fin (coordinateBound n d)) := Finset.univ.toList

def candidate (n : ℕ) (s : Fin d → Fin (coordinateBound n d)) (y : K) : K :=
  basis.equivFun.symm (fun i => ((PowerRootCoordinateCandidates.candidates basis n i y).drop (s i).val).headD 0)

def candidates (n : ℕ) (y : K) : List K := (choices n d).map (fun s => candidate basis n s y)

def roots (n : ℕ) (y : K) : List K := (candidates basis n y).filter (fun x => decide (x^n=y))

theorem headD_drop_eq_getElem {A : Type} (xs : List A) (a : A) (k : ℕ) (hk : k < xs.length) :
    (xs.drop k).headD a = xs[k] := by
  rw [List.headD_eq_head?_getD, List.head?_drop, List.getElem?_eq_getElem hk]
  rfl

theorem root_mem_candidates (n : ℕ) (hn : 0 < n) (x : K) : x ∈ candidates basis n (x^n) := by
  have hi (i : Fin d) := List.getElem_of_mem (PowerRootCoordinateCandidates.coordinate_mem basis n hn i x)
  choose k hk he using hi
  have hk' (i : Fin d) : k i < coordinateBound n d :=
    (hk i).trans_le (PowerRootCoordinateCandidates.candidates_length basis n i (x^n))
  let s : Fin d → Fin (coordinateBound n d) := fun i => ⟨k i, hk' i⟩
  apply List.mem_map.mpr
  refine ⟨s, by simp [choices], ?_⟩
  apply basis.equivFun.injective
  simp only [candidate, basis.equivFun.apply_symm_apply]
  funext i
  exact (headD_drop_eq_getElem _ 0 (k i) (hk i)).trans (he i)

theorem mem_roots_iff (n : ℕ) (hn : 0 < n) (x y : K) :
    x ∈ roots basis n y ↔ x^n=y := by
  simp only [roots, List.mem_filter, decide_eq_true_eq]
  exact ⟨And.right, fun h => ⟨h ▸ root_mem_candidates basis n hn x, h⟩⟩

theorem fp_candidate (n : ℕ) (s : Fin d → Fin (coordinateBound n d)) :
    FP (numberFieldEncoding basis) (numberFieldEncoding basis) (candidate basis n s) := by
  apply FixedFieldArithmetic.fp_of_coordinates
  intro i
  have hc := PowerRootCoordinateCandidates.fp_candidates basis n i
  have hd := ((fp_const (numberFieldEncoding basis) BitEncoding.nat (s i).val).pair hc).comp
    (ListDropMachines.fp_drop BitEncoding.rat 0)
  exact (hd.comp (ListDecompositionMachines.fp_headD BitEncoding.rat 0)).congr
    (fun y => by simp only [Function.comp_apply, candidate, basis.equivFun.apply_symm_apply])

theorem fp_fixedList {A B : Type} (ea : BitEncoding A) (eb : BitEncoding B)
    (fs : List (A → B)) (hf : ∀ f ∈ fs, FP ea eb f) :
    FP ea eb.list (fun a => fs.map (fun f => f a)) := by
  induction fs with
  | nil => exact fp_const ea eb.list []
  | cons f fs ih =>
    have ht := ih (fun g hg => hf g (by simp [hg]))
    exact (((hf f (by simp)).pair ht).comp (ListMutationMachines.fp_cons eb)).congr (fun _ => rfl)

theorem fp_candidates (n : ℕ) :
    FP (numberFieldEncoding basis) (numberFieldEncoding basis).list (candidates basis n) := by
  have h := fp_fixedList (numberFieldEncoding basis) (numberFieldEncoding basis)
    ((choices n d).map (fun s => candidate basis n s)) (by
      intro f hf
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hf
      exact fp_candidate basis n s)
  exact h.congr (fun y => by simp [candidates])

theorem fp_roots (n : ℕ) :
    FP (numberFieldEncoding basis) (numberFieldEncoding basis).list (roots basis n) := by
  have hy := fp_fst (numberFieldEncoding basis) (numberFieldEncoding basis)
  have hx := fp_snd (numberFieldEncoding basis) (numberFieldEncoding basis)
  have hp := hx.comp (FixedFieldPolynomialMachines.fp_fixedPower basis n)
  have ht := (hp.pair hy).comp (FixedFieldArithmetic.fp_equality basis)
  exact ((fp_id (numberFieldEncoding basis)).pair (fp_candidates basis n)).comp
    (ListContextFilterMachines.fp_filterWithContext (numberFieldEncoding basis)
      (numberFieldEncoding basis) (fun p => decide (p.2^n=p.1)) ht)

end PlanarHom.FixedFieldPowerRootCandidates
