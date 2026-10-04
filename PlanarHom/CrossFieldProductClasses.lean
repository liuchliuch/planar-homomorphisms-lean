import PlanarHom.CrossFieldInterpolationSemantics
import PlanarHom.FixedLengthProductRecovery

/-! Exact retained exponent classes across two different coefficient fields. -/
noncomputable section
namespace PlanarHom.SourceExponentRepresentatives
open ExponentProductSemantics
variable {K L : Type} [Field K] [Field L] [DecidableEq K] {t : ℕ}

def sourceNode (A : Fin t → K) (m : ℕ) (i : Fin (representatives A m).length) : K :=
  ((representatives A m).get i).1

def exponents (A : Fin t → K) (m : ℕ) (i : Fin (representatives A m).length) : List ℕ :=
  ((representatives A m).get i).2

def CrossCompatibleAt (A : Fin t → K) (B : Fin t → L) (m : ℕ) : Prop :=
  ∀ xs ∈ ExponentVectors.weak t m, ∀ ys ∈ ExponentVectors.weak t m,
    value A xs ≠ 0 → value A xs = value A ys → value B xs = value B ys

theorem sourceNode_nonzero (A : Fin t → K) (m : ℕ) (i : Fin (representatives A m).length) :
    sourceNode A m i ≠ 0 := (mem_representatives A m _ (List.get_mem _ i)).2.2

theorem sourceNode_injective (A : Fin t → K) (m : ℕ) : Function.Injective (sourceNode A m) := by
  intro i j he
  have hp := List.pairwise_iff_get.mp (representatives_pairwise A m)
  by_contra hij
  have hv : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hv with hlt | hgt
  · exact hp i j hlt he
  · exact hp j i hgt he.symm

theorem representatives_eq_ofFn (A : Fin t → K) (m : ℕ) :
    representatives A m = List.ofFn (fun i => (sourceNode A m i, exponents A m i)) := by
  simpa only [sourceNode, exponents] using (List.ofFn_get (representatives A m)).symm

/-- Coverage retains the correct target in any extension field under exactly
the current-length cross-field collision condition. -/
theorem exists_node_for_weak (A : Fin t → K) (B : Fin t → L) {m : ℕ}
    (h : CrossCompatibleAt A B m) (xs : List ℕ) (hxs : xs ∈ ExponentVectors.weak t m)
    (hz : value A xs ≠ 0) :
    ∃ i : Fin (representatives A m).length,
      sourceNode A m i = value A xs ∧ value B (exponents A m i) = value B xs := by
  obtain ⟨row, hr, he⟩ := representatives_coverage A m xs hxs hz
  have hm := mem_representatives A m row hr
  have ht := h xs hxs row.2 hm.1 hz (he.symm.trans hm.2.1)
  obtain ⟨i, hi⟩ := List.get_of_mem hr
  refine ⟨i, ?_, ?_⟩
  · change ((representatives A m).get i).1 = value A xs
    rw [hi]
    exact he
  · change value B ((representatives A m).get i).2 = value B xs
    rw [hi]
    exact ht.symm

/-- Exact heterogeneous-field list recovery from its computed source-key table. -/
theorem aggregate_computed_table (φ : K →+* L) (A : Fin t → K) (B : Fin t → L) (m : ℕ)
    (y : Fin (representatives A m).length → K) :
    CrossFieldInterpolationSemantics.aggregate φ B (representatives A m) (List.ofFn y) =
      ∑ j, φ (CrossFieldInterpolationSemantics.rowWeight (sourceNode A m) y j) *
        value B (exponents A m j) := by
  calc
    _ = CrossFieldInterpolationSemantics.aggregate φ B
        (List.ofFn (fun i => (sourceNode A m i, exponents A m i))) (List.ofFn y) :=
      congrArg (fun rows => CrossFieldInterpolationSemantics.aggregate φ B rows (List.ofFn y))
        (representatives_eq_ofFn A m)
    _ = _ := by
      exact CrossFieldInterpolationSemantics.aggregate_ofFn φ B _ _ _ (sourceNode_injective A m)

end PlanarHom.SourceExponentRepresentatives
