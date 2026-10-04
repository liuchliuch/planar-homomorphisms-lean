import PlanarHom.PlanarEmbedding
import Mathlib.Data.Real.Archimedean

/-!
# Arbitrary positive-length stretching preserves ordinary planarity

Each occurrence, including every loop, is replaced by a path of length `n + 1`,
with `n` private internal vertices. The proof constructs the new drawing by affine
restriction of its original curve, with no edge-neighborhood assumption.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph

/-- Source of the `k`th segment of a stretched edge. -/
def stretchSrc {V E : Type*} (G : MultiGraph V E) (n : ℕ) (p : E × Fin (n+1)) :
    V ⊕ (E × Fin n) :=
  if h : p.2.val = 0 then Sum.inl (G.src p.1)
  else Sum.inr (p.1, ⟨p.2.val - 1, by omega⟩)

/-- Destination of the `k`th segment of a stretched edge. -/
def stretchDst {V E : Type*} (G : MultiGraph V E) (n : ℕ) (p : E × Fin (n+1)) :
    V ⊕ (E × Fin n) :=
  if h : p.2.val = n then Sum.inl (G.dst p.1)
  else Sum.inr (p.1, ⟨p.2.val, by omega⟩)

/-- Positive-length stretching, with all edge and vertex occurrences explicit. -/
def stretch {V E : Type*} (G : MultiGraph V E) (n : ℕ) :
    MultiGraph (V ⊕ (E × Fin n)) (E × Fin (n+1)) where
  src := G.stretchSrc n
  dst := G.stretchDst n

namespace PlaneDrawing

/-- Parameter for a newly inserted internal vertex. -/
def knot {n : ℕ} (k : Fin n) : I :=
  ⟨((k.val : ℝ) + 1) / ((n : ℝ) + 1), by
    have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
    constructor
    · exact div_nonneg (by positivity) (by positivity)
    · exact (div_le_one (by positivity)).mpr (by linarith)⟩

theorem knot_inside {n : ℕ} (k : Fin n) : Inside (knot k) := by
  have hk : (k.val : ℝ) + 1 ≤ n := by exact_mod_cast k.isLt
  constructor
  · exact div_pos (by positivity) (by positivity)
  · exact (div_lt_one (by positivity)).mpr (by linarith)

theorem knot_injective {n : ℕ} : Function.Injective (@knot n) := by
  intro k l h
  have hh := congrArg (fun t : I => (t : ℝ)) h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he := (div_left_inj' hn).mp hh
  apply Fin.ext
  exact_mod_cast (add_right_cancel he)

/-- The affine restriction to segment `k`. -/
def segmentParameter (n : ℕ) (k : Fin (n+1)) : C(I, I) where
  toFun t := ⟨((k.val : ℝ) + (t : ℝ)) / ((n : ℝ) + 1), by
    have hk : (k.val : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp k.isLt)
    constructor
    · exact div_nonneg (add_nonneg (Nat.cast_nonneg _) t.2.1) (by positivity)
    · exact (div_le_one (by positivity)).mpr (by linarith [t.2.2])⟩
  continuous_toFun := by fun_prop

theorem segmentParameter_inside {n : ℕ} (k : Fin (n+1)) {t : I} (ht : Inside t) :
    Inside (segmentParameter n k t) := by
  have hk : (k.val : ℝ) ≤ n := by exact_mod_cast (Nat.lt_succ_iff.mp k.isLt)
  constructor
  · exact div_pos (by linarith [Nat.cast_nonneg (α := ℝ) k.val, ht.1]) (by positivity)
  · exact (div_lt_one (by positivity)).mpr (by linarith [ht.2])

theorem segmentParameter_injective {n : ℕ} (k l : Fin (n+1)) {s t : I}
    (hs : Inside s) (ht : Inside t) (h : segmentParameter n k s = segmentParameter n l t) :
    k = l ∧ s = t := by
  have hh := congrArg (fun u : I => (u : ℝ)) h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he := (div_left_inj' hn).mp hh
  rcases lt_trichotomy k.val l.val with hkl | hkl | hkl
  · have hc : (k.val : ℝ) + 1 ≤ l.val := by exact_mod_cast hkl
    exfalso
    linarith [hs.2, ht.1]
  · exact ⟨Fin.ext hkl, Subtype.ext (by simpa [hkl] using he)⟩
  · have hc : (l.val : ℝ) + 1 ≤ k.val := by exact_mod_cast hkl
    exfalso
    linarith [hs.1, ht.2]

theorem segmentParameter_ne_knot {n : ℕ} (k : Fin (n+1)) (l : Fin n)
    {t : I} (ht : Inside t) : segmentParameter n k t ≠ knot l := by
  intro h
  have hh := congrArg (fun u : I => (u : ℝ)) h
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  have he := (div_left_inj' hn).mp hh
  by_cases hkl : k.val ≤ l.val
  · have hc : (k.val : ℝ) ≤ l.val := by exact_mod_cast hkl
    linarith [ht.2]
  · have hc : (l.val : ℝ) + 1 ≤ k.val := by exact_mod_cast (Nat.lt_of_not_ge hkl)
    linarith [ht.1]

variable {V E : Type*} {G : MultiGraph V E}

/-- Actual vertex positions in the stretched drawing. -/
def stretchPoint (d : PlaneDrawing G) (n : ℕ) : V ⊕ (E × Fin n) → Plane :=
  Sum.elim d.point (fun p => d.curve p.1 (knot p.2))

theorem stretchPoint_src (d : PlaneDrawing G) (n : ℕ) (p : E × Fin (n+1)) :
    d.stretchPoint n (G.stretchSrc n p) = d.curve p.1 (segmentParameter n p.2 0) := by
  by_cases hk : p.2.val = 0
  · have hp : segmentParameter n p.2 0 = 0 := by
      apply Subtype.ext
      simp [segmentParameter, hk]
    simp [stretchSrc, hk, stretchPoint, hp, d.curve_zero]
  · have hp : knot (⟨p.2.val - 1, by omega⟩ : Fin n) = segmentParameter n p.2 0 := by
      apply Subtype.ext
      dsimp [knot, segmentParameter]
      rw [Nat.cast_sub (by omega : 1 ≤ p.2.val)]
      simp
    simp only [stretchSrc, hk, ↓reduceDIte, stretchPoint, Sum.elim_inr]
    exact congrArg (d.curve p.1) hp

theorem stretchPoint_dst (d : PlaneDrawing G) (n : ℕ) (p : E × Fin (n+1)) :
    d.stretchPoint n (G.stretchDst n p) = d.curve p.1 (segmentParameter n p.2 1) := by
  by_cases hk : p.2.val = n
  · have hp : segmentParameter n p.2 1 = 1 := by
      apply Subtype.ext
      dsimp [segmentParameter]
      rw [hk]
      exact div_self (by positivity)
    simp [stretchDst, hk, stretchPoint, hp, d.curve_one]
  · have hp : knot (⟨p.2.val, by omega⟩ : Fin n) = segmentParameter n p.2 1 := rfl
    simp only [stretchDst, hk, ↓reduceDIte, stretchPoint, Sum.elim_inr]
    exact congrArg (d.curve p.1) hp

/-- Construct every segment by affine reparameterization of the old edge. -/
def stretch (d : PlaneDrawing G) (n : ℕ) : PlaneDrawing (G.stretch n) where
  point := d.stretchPoint n
  point_injective := by
    intro x y h
    cases x with
    | inl v =>
      cases y with
      | inl w => exact congrArg Sum.inl (d.point_injective h)
      | inr q => exact False.elim (d.interior_avoids q.1 _ (knot_inside q.2) v h.symm)
    | inr p =>
      cases y with
      | inl w => exact False.elim (d.interior_avoids p.1 _ (knot_inside p.2) w h)
      | inr q =>
        obtain ⟨he,hv⟩ := d.interior_injective p.1 q.1 _ _
          (knot_inside p.2) (knot_inside q.2) h
        exact congrArg Sum.inr (Prod.ext he (knot_injective hv))
  curve p := (d.curve p.1).comp (segmentParameter n p.2)
  curve_zero p := (d.stretchPoint_src n p).symm
  curve_one p := (d.stretchPoint_dst n p).symm
  interior_injective := by
    rintro ⟨e,k⟩ ⟨f,l⟩ s t hs ht h
    obtain ⟨hef,hab⟩ := d.interior_injective e f _ _
      (segmentParameter_inside k hs) (segmentParameter_inside l ht) h
    obtain ⟨hkl,hst⟩ := segmentParameter_injective k l hs ht hab
    exact ⟨Prod.ext hef hkl,hst⟩
  interior_avoids := by
    rintro ⟨e,k⟩ t ht (v | p) h
    · exact d.interior_avoids e _ (segmentParameter_inside k ht) v h
    · have hq := (d.interior_injective e p.1 _ _
        (segmentParameter_inside k ht) (knot_inside p.2) h).2
      exact segmentParameter_ne_knot k p.2 ht hq

/-- All old curve parameters occur in some new segment. -/
theorem exists_segmentParameter (n : ℕ) (t : I) :
    ∃ k : Fin (n+1), ∃ s : I, segmentParameter n k s = t := by
  have hn : (0 : ℝ) < n + 1 := by positivity
  by_cases ht : t = 1
  · refine ⟨⟨n, Nat.lt_succ_self n⟩, 1, ?_⟩
    apply Subtype.ext
    simp [segmentParameter, ht, ne_of_gt hn]
  · have ht1 : (t : ℝ) < 1 := lt_of_le_of_ne t.2.2
      (fun h => ht (Subtype.ext h))
    let u : ℝ := ((n : ℝ) + 1) * t
    have hu0 : 0 ≤ u := mul_nonneg hn.le t.2.1
    have hu1 : u < n + 1 := by dsimp [u]; nlinarith
    have hm : Nat.floor u < n + 1 := (Nat.floor_lt hu0).mpr (by simpa using hu1)
    have hfloor := Nat.floor_le hu0
    have hceil := Nat.lt_floor_add_one u
    refine ⟨⟨Nat.floor u,hm⟩, ⟨u - (Nat.floor u : ℝ), ?_⟩, ?_⟩
    · constructor <;> linarith
    · apply Subtype.ext
      dsimp [segmentParameter]
      apply (div_eq_iff (ne_of_gt hn)).mpr
      dsimp [u]
      ring

/-- Stretching preserves the entire drawn subset, so also preserves every face. -/
@[simp] theorem support_stretch (d : PlaneDrawing G) (n : ℕ) :
    (d.stretch n).support = d.support := by
  ext x
  simp only [support, Set.mem_union, Set.mem_range, Set.mem_iUnion]
  constructor
  · rintro (⟨v,hv⟩ | ⟨⟨e,k⟩,t,ht⟩)
    · cases v with
      | inl v => exact Or.inl ⟨v,hv⟩
      | inr p => exact Or.inr ⟨p.1,knot p.2,hv⟩
    · exact Or.inr ⟨e,segmentParameter n k t,ht⟩
  · rintro (⟨v,hv⟩ | ⟨e,t,ht⟩)
    · exact Or.inl ⟨Sum.inl v,hv⟩
    · obtain ⟨k,s,hs⟩ := exists_segmentParameter n t
      exact Or.inr ⟨(e,k),s,by simpa [stretch, hs] using ht⟩

@[simp] theorem cofacial_stretch_iff (d : PlaneDrawing G) (n : ℕ) (u v : V) :
    (d.stretch n).Cofacial (Sum.inl u) (Sum.inl v) ↔ d.Cofacial u v := by
  simp only [Cofacial, support_stretch]; rfl

@[simp] theorem outerCofacial_stretch_iff (d : PlaneDrawing G) (n : ℕ) (u v : V) :
    (d.stretch n).OuterCofacial (Sum.inl u) (Sum.inl v) ↔ d.OuterCofacial u v := by
  simp only [OuterCofacial, support_stretch]; rfl

end PlaneDrawing

/-- Every positive path length is allowed, on arbitrary abstract planar inputs.
For `n = 0`, one segment replaces each old edge and no new vertices are added. -/
theorem Planar.stretch {V E : Type*} {G : MultiGraph V E} (h : G.Planar) (n : ℕ) :
    (G.stretch n).Planar := h.map (fun d => d.stretch n)

end PlanarHom.MultiGraph
