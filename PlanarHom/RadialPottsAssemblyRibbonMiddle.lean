import PlanarHom.OccurrenceKasteleynPolygonalCollars

/-!
NEW compatibility adaptation: only the import has changed. The recovered proof
body below is preserved. It uses the ordinary baseline RibbonDrawing API; no
missing normal, face-enumeration, or orientation theorem is required.

# Closed middle rectangles in the actual occurrence ribbons

Trimming only the longitudinal coordinate removes the pinched endpoints. Every
result here is about the closed square, including its four sides and corners.
Different edge occurrences have disjoint images even for loops and parallel
occurrences. The results deliberately assert no routing around host vertices.
-/

noncomputable section
open Set unitInterval
namespace PlanarHom.MultiGraph.RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A closed affine subinterval, with its original increasing orientation. -/
def middleParameter (a b : I) (hab : a ≤ b) : C(I,I) where
  toFun t := ⟨(a : ℝ)+((b : ℝ)-a)*(t : ℝ), by
    have ht0 := t.property.1
    have ht1 := t.property.2
    have hab' : (a : ℝ) ≤ b := hab
    constructor
    · nlinarith [a.property.1]
    · nlinarith [b.property.2]⟩
  continuous_toFun := by fun_prop

@[simp] theorem middleParameter_zero (a b : I) (hab : a ≤ b) :
    middleParameter a b hab 0 = a := by
  apply Subtype.ext
  simp [middleParameter]

@[simp] theorem middleParameter_one (a b : I) (hab : a ≤ b) :
    middleParameter a b hab 1 = b := by
  apply Subtype.ext
  simp [middleParameter]

theorem middleParameter_bounds (a b : I) (hab : a ≤ b) (t : I) :
    a ≤ middleParameter a b hab t ∧ middleParameter a b hab t ≤ b := by
  have hab' : (a : ℝ) ≤ b := hab
  have ht0 := t.property.1
  have ht1 := t.property.2
  constructor <;> change (_ : ℝ) ≤ _ <;> dsimp [middleParameter] <;> nlinarith

theorem middleParameter_inside (a b : I) (hab : a ≤ b)
    (ha : Inside a) (hb : Inside b) (t : I) :
    Inside (middleParameter a b hab t) := by
  obtain ⟨hl,hu⟩ := middleParameter_bounds a b hab t
  exact ⟨lt_of_lt_of_le ha.1 hl,lt_of_le_of_lt hu hb.2⟩

theorem middleParameter_strictMono (a b : I) (hab : a < b) :
    StrictMono (middleParameter a b hab.le) := by
  intro s t hst
  change (a : ℝ)+((b : ℝ)-a)*(s : ℝ) < (a : ℝ)+((b : ℝ)-a)*(t : ℝ)
  have hs : (s : ℝ) < t := hst
  have hh : (a : ℝ) < b := hab
  nlinarith

/-- Longitudinal trimming retains the entire closed transverse interval. -/
def middleSquare (a b : I) (hab : a ≤ b) : C(I × I,I × I) where
  toFun p := (middleParameter a b hab p.1,p.2)
  continuous_toFun := by fun_prop

/-- The actual closed middle band of an occurrence, as a continuous square map. -/
def middleBand (R : RibbonDrawing G) (a b : I) (hab : a ≤ b) (e : E) :
    C(I × I,Plane) := (R.band e).comp (middleSquare a b hab)

@[simp] theorem middleBand_apply (R : RibbonDrawing G) (a b : I) (hab : a ≤ b)
    (e : E) (p : I × I) :
    R.middleBand a b hab e p = R.band e (middleParameter a b hab p.1,p.2) := rfl

/-- Equality anywhere on the closed middle bands recovers the occurrence and
both coordinates. Neither transverse coordinate is required to be interior. -/
theorem middleBand_injective (R : RibbonDrawing G) (a b : I) (hab : a < b)
    (ha : Inside a) (hb : Inside b) (e f : E) (p q : I × I)
    (h : R.middleBand a b hab.le e p = R.middleBand a b hab.le f q) :
    e = f ∧ p = q := by
  obtain ⟨hef,hpq⟩ := R.band_injective e f _ _
    (middleParameter_inside a b hab.le ha hb p.1)
    (middleParameter_inside a b hab.le ha hb q.1) h
  change (middleParameter a b hab.le p.1,p.2) =
    (middleParameter a b hab.le q.1,q.2) at hpq
  refine ⟨hef,?_⟩
  apply Prod.ext
  · exact (middleParameter_strictMono a b hab).injective (congrArg (fun z : I × I => z.1) hpq)
  · have hh := congrArg (fun z : I × I => z.2) hpq
    exact hh

/-- Every occurrence's whole closed middle square is a closed topological embedding. -/
theorem middleBand_isClosedEmbedding (R : RibbonDrawing G) (a b : I) (hab : a < b)
    (ha : Inside a) (hb : Inside b) (e : E) :
    Topology.IsClosedEmbedding (R.middleBand a b hab.le e) := by
  apply (R.middleBand a b hab.le e).continuous.isClosedEmbedding
  intro p q h
  exact (R.middleBand_injective a b hab ha hb e e p q h).2

/-- Closed middle rectangles of different edge occurrences are disjoint. -/
theorem middleBand_disjoint (R : RibbonDrawing G) (a b : I) (hab : a < b)
    (ha : Inside a) (hb : Inside b) {e f : E} (hef : e ≠ f) :
    Disjoint (Set.range (R.middleBand a b hab.le e))
      (Set.range (R.middleBand a b hab.le f)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,rfl⟩ ⟨q,hq⟩
  exact hef (R.middleBand_injective a b hab ha hb e f p q hq.symm).1

/-- Trimming also separates the entire closed band from every old vertex. -/
theorem middleBand_avoids (R : RibbonDrawing G) (a b : I) (hab : a ≤ b)
    (ha : Inside a) (hb : Inside b) (e : E) (p : I × I) (v : V) :
    R.middleBand a b hab e p ≠ R.point v :=
  R.band_avoids e _ (middleParameter_inside a b hab ha hb p.1) v

/-- The left and right cuts retain all distinct transverse port positions. -/
theorem middleBand_cut_injective (R : RibbonDrawing G) (a b : I) (hab : a < b)
    (ha : Inside a) (hb : Inside b) (e : E) (t : I) :
    Function.Injective (fun s : I => R.middleBand a b hab.le e (t,s)) := by
  intro s u h
  exact congrArg Prod.snd (R.middleBand_injective a b hab ha hb e e (t,s) (t,u) h).2

end PlanarHom.MultiGraph.RibbonDrawing

namespace PlanarHom.MultiGraph.RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- A transverse-dependent pair of cuts, e.g. obtained by meeting a vertex
circle at a different longitudinal parameter for each height. -/
def clippedSquare (a b : C(I,I)) (hab : ∀ s, a s ≤ b s) : C(I × I,I × I) where
  toFun p := (middleParameter (a p.2) (b p.2) (hab p.2) p.1,p.2)
  continuous_toFun := by
    apply Continuous.prodMk
    · apply Continuous.subtype_mk
      change Continuous (fun p : I × I => (a p.2 : ℝ)+((b p.2 : ℝ)-a p.2)*(p.1 : ℝ))
      fun_prop
    · exact continuous_snd

/-- The original ribbon with a possibly curved cut at each end. -/
def clippedBand (R : RibbonDrawing G) (a b : C(I,I)) (hab : ∀ s, a s ≤ b s) (e : E) :
    C(I × I,Plane) := (R.band e).comp (clippedSquare a b hab)

@[simp] theorem clippedBand_zero (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s ≤ b s) (e : E) (s : I) :
    R.clippedBand a b hab e (0,s) = R.band e (a s,s) := by
  change R.band e (middleParameter (a s) (b s) (hab s) 0,s) = _
  rw [middleParameter_zero]

@[simp] theorem clippedBand_one (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s ≤ b s) (e : E) (s : I) :
    R.clippedBand a b hab e (1,s) = R.band e (b s,s) := by
  change R.band e (middleParameter (a s) (b s) (hab s) 1,s) = _
  rw [middleParameter_one]

/-- Recover an occurrence and both square coordinates for transverse-dependent
cuts. This is the closed-band separation needed by nonconstant circle cuts. -/
theorem clippedBand_injective (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s < b s) (ha : ∀ s, Inside (a s)) (hb : ∀ s, Inside (b s))
    (e f : E) (p q : I × I)
    (h : R.clippedBand a b (fun s => (hab s).le) e p =
      R.clippedBand a b (fun s => (hab s).le) f q) : e = f ∧ p = q := by
  rcases p with ⟨t,s⟩
  rcases q with ⟨u,v⟩
  obtain ⟨hef,hpq⟩ := R.band_injective e f _ _
    (middleParameter_inside (a s) (b s) (hab s).le (ha s) (hb s) t)
    (middleParameter_inside (a v) (b v) (hab v).le (ha v) (hb v) u) h
  have hs := congrArg (fun p : I × I => p.2) hpq
  change s = v at hs
  subst v
  have ht := congrArg (fun p : I × I => p.1) hpq
  have htu := (middleParameter_strictMono (a s) (b s) (hab s)).injective ht
  exact ⟨hef,Prod.ext htu rfl⟩

/-- The whole variably clipped band remains a closed embedding. -/
theorem clippedBand_isClosedEmbedding (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s < b s) (ha : ∀ s, Inside (a s)) (hb : ∀ s, Inside (b s)) (e : E) :
    Topology.IsClosedEmbedding (R.clippedBand a b (fun s => (hab s).le) e) := by
  apply (R.clippedBand a b (fun s => (hab s).le) e).continuous.isClosedEmbedding
  intro p q h
  exact (R.clippedBand_injective a b hab ha hb e e p q h).2

/-- Variable cuts retain disjointness between different occurrences. -/
theorem clippedBand_disjoint (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s < b s) (ha : ∀ s, Inside (a s)) (hb : ∀ s, Inside (b s))
    {e f : E} (hef : e ≠ f) :
    Disjoint (Set.range (R.clippedBand a b (fun s => (hab s).le) e))
      (Set.range (R.clippedBand a b (fun s => (hab s).le) f)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,rfl⟩ ⟨q,hq⟩
  exact hef (R.clippedBand_injective a b hab ha hb e f p q hq.symm).1

end PlanarHom.MultiGraph.RibbonDrawing

namespace PlanarHom.MultiGraph.RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

/-- An injective continuous change of transverse coordinates gives another
actual ribbon, without repeating any good-width argument. -/
def mapTransverse (R : RibbonDrawing G) (f : C(I,I)) (hf : Function.Injective f) :
    RibbonDrawing G where
  point := R.point
  point_injective := R.point_injective
  band e := (R.band e).comp ⟨fun p => (p.1,f p.2),by fun_prop⟩
  band_zero e s := R.band_zero e (f s)
  band_one e s := R.band_one e (f s)
  band_injective := by
    intro e g p q hp hq h
    obtain ⟨heg,hpq⟩ := R.band_injective e g (p.1,f p.2) (q.1,f q.2) hp hq h
    have ht := congrArg (fun z : I × I => z.1) hpq
    have hs := congrArg (fun z : I × I => z.2) hpq
    exact ⟨heg,Prod.ext ht (hf hs)⟩
  band_avoids e p hp v := R.band_avoids e (p.1,f p.2) hp v

@[simp] theorem mapTransverse_apply (R : RibbonDrawing G) (f : C(I,I))
    (hf : Function.Injective f) (e : E) (p : I × I) :
    (R.mapTransverse f hf).band e p = R.band e (p.1,f p.2) := rfl

/-- Restriction to transverse heights in `[0,η]`, with `η > 0`. -/
def narrow (R : RibbonDrawing G) (η : I) (hη : 0 < η) : RibbonDrawing G :=
  R.mapTransverse (middleParameter 0 η hη.le) (middleParameter_strictMono 0 η hη).injective

@[simp] theorem narrow_apply (R : RibbonDrawing G) (η : I) (hη : 0 < η)
    (e : E) (t s : I) :
    (R.narrow η hη).band e (t,s) = R.band e (t,middleParameter 0 η hη.le s) := rfl

@[simp] theorem narrow_height (η : I) (hη : 0 < η) (s : I) :
    (middleParameter 0 η hη.le s : ℝ) = (η : ℝ)*(s : ℝ) := by
  simp [middleParameter]

/-- Each occurrence may have its own two variable end cuts. Distinct original
occurrences still have disjoint closed images. -/
theorem clippedBand_disjoint_of_cuts (R : RibbonDrawing G) (a b c d : C(I,I))
    (hab : ∀ s, a s ≤ b s) (hcd : ∀ s, c s ≤ d s)
    (ha : ∀ s, Inside (a s)) (hb : ∀ s, Inside (b s))
    (hc : ∀ s, Inside (c s)) (hd : ∀ s, Inside (d s)) {e f : E} (hef : e ≠ f) :
    Disjoint (Set.range (R.clippedBand a b hab e)) (Set.range (R.clippedBand c d hcd f)) := by
  apply Set.disjoint_left.mpr
  rintro x ⟨p,rfl⟩ ⟨q,hq⟩
  exact hef (R.band_injective e f _ _
    (middleParameter_inside _ _ _ (ha p.2) (hb p.2) p.1)
    (middleParameter_inside _ _ _ (hc q.2) (hd q.2) q.1) hq.symm).1

/-- Every point of an occurrence-dependent clipped band avoids every host. -/
theorem clippedBand_avoids (R : RibbonDrawing G) (a b : C(I,I))
    (hab : ∀ s, a s ≤ b s) (ha : ∀ s, Inside (a s)) (hb : ∀ s, Inside (b s))
    (e : E) (p : I × I) (v : V) : R.clippedBand a b hab e p ≠ R.point v :=
  R.band_avoids e _ (middleParameter_inside _ _ _ (ha p.2) (hb p.2) p.1) v

/-- Finiteness and compactness give one positive disk clearance simultaneously
for every closed middle band and every old vertex, with no nonemptiness premise. -/
theorem middleBand_uniform_clearance [Finite V] [Finite E] (R : RibbonDrawing G)
    (a b : I) (hab : a ≤ b) (ha : Inside a) (hb : Inside b) :
    ∃ r : ℝ, 0 < r ∧ ∀ e p v, r < dist (R.middleBand a b hab e p) (R.point v) := by
  let S : Set Plane := ⋃ e, Set.range (R.middleBand a b hab e)
  have hS : IsCompact S := isCompact_iUnion fun e => isCompact_range (R.middleBand a b hab e).continuous
  have hH : IsClosed (Set.range R.point) := (Set.finite_range R.point).isClosed
  have hdis : Disjoint S (Set.range R.point) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨v,rfl⟩
    obtain ⟨e,p,hp⟩ := Set.mem_iUnion.mp hx
    exact R.middleBand_avoids a b hab ha hb e p v hp
  obtain ⟨r,hr,hsep⟩ := EMetric.exists_pos_forall_lt_edist hS hH hdis
  refine ⟨r,hr,?_⟩
  intro e p v
  have hh := hsep _ (Set.mem_iUnion.mpr ⟨e,p,rfl⟩) _ ⟨v,rfl⟩
  have hreal := (ENNReal.toReal_lt_toReal (by simp) (edist_ne_top _ _)).mpr hh
  simpa using hreal

end PlanarHom.MultiGraph.RibbonDrawing

namespace PlanarHom.MultiGraph.RibbonDrawing
variable {V E : Type*} {G : MultiGraph V E}

@[simp] theorem mapTransverse_point (R : RibbonDrawing G) (f : C(I,I))
    (hf : Function.Injective f) (v : V) : (R.mapTransverse f hf).point v = R.point v := rfl

@[simp] theorem narrow_point (R : RibbonDrawing G) (η : I) (hη : 0 < η) (v : V) :
    (R.narrow η hη).point v = R.point v := rfl

/-- Every original parameter between the two cuts appears in the middle square. -/
theorem middleParameter_surjective_Icc (a b : I) (hab : a < b) {t : I}
    (hat : a ≤ t) (htb : t ≤ b) : ∃ u : I, middleParameter a b hab.le u = t := by
  have hab' : (a : ℝ) < b := hab
  have hat' : (a : ℝ) ≤ t := hat
  have htb' : (t : ℝ) ≤ b := htb
  let u : I := ⟨((t : ℝ)-a)/((b : ℝ)-a),div_nonneg (sub_nonneg.mpr hat')
    (sub_pos.mpr hab').le,(div_le_one (sub_pos.mpr hab')).mpr (by linarith)⟩
  refine ⟨u,Subtype.ext ?_⟩
  change (a : ℝ)+((b : ℝ)-a)*(((t : ℝ)-a)/((b : ℝ)-a)) = t
  field_simp [ne_of_gt (sub_pos.mpr hab')]
  ring

/-- Direct clearance statement in the original ribbon parameters. Any positive
endpoint cutoff works, including cutoffs far smaller than one third. -/
theorem central_uniform_clearance [Finite V] [Finite E] (R : RibbonDrawing G)
    (a b : I) (hab : a < b) (ha : Inside a) (hb : Inside b) :
    ∃ r : ℝ, 0 < r ∧ ∀ e t s v, a ≤ t → t ≤ b → r < dist (R.band e (t,s)) (R.point v) := by
  obtain ⟨r,hr,hsep⟩ := R.middleBand_uniform_clearance a b hab.le ha hb
  refine ⟨r,hr,?_⟩
  intro e t s v hat htb
  obtain ⟨u,hu⟩ := middleParameter_surjective_Icc a b hab hat htb
  have hh := hsep e (u,s) v
  simpa only [middleBand_apply,hu] using hh

/-- Fully occurrence-dependent continuous cuts also have one compact clearance
from every old vertex. Empty occurrence/vertex types require no special case. -/
theorem clippedBand_uniform_clearance [Finite V] [Finite E] (R : RibbonDrawing G)
    (a b : E → C(I,I)) (hab : ∀ e s, a e s ≤ b e s)
    (ha : ∀ e s, Inside (a e s)) (hb : ∀ e s, Inside (b e s)) :
    ∃ r : ℝ, 0 < r ∧ ∀ e p v, r < dist (R.clippedBand (a e) (b e) (hab e) e p) (R.point v) := by
  let S : Set Plane := ⋃ e, Set.range (R.clippedBand (a e) (b e) (hab e) e)
  have hS : IsCompact S := isCompact_iUnion fun e =>
    isCompact_range (R.clippedBand (a e) (b e) (hab e) e).continuous
  have hH : IsClosed (Set.range R.point) := (Set.finite_range R.point).isClosed
  have hdis : Disjoint S (Set.range R.point) := by
    apply Set.disjoint_left.mpr
    rintro x hx ⟨v,rfl⟩
    obtain ⟨e,p,hp⟩ := Set.mem_iUnion.mp hx
    exact R.clippedBand_avoids (a e) (b e) (hab e) (ha e) (hb e) e p v hp
  obtain ⟨r,hr,hsep⟩ := EMetric.exists_pos_forall_lt_edist hS hH hdis
  refine ⟨r,hr,?_⟩
  intro e p v
  have hh := hsep _ (Set.mem_iUnion.mpr ⟨e,p,rfl⟩) _ ⟨v,rfl⟩
  have hreal := (ENNReal.toReal_lt_toReal (by simp) (edist_ne_top _ _)).mpr hh
  simpa using hreal

end PlanarHom.MultiGraph.RibbonDrawing
