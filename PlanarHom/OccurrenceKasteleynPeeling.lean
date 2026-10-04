import PlanarHom.PlanarRibbons
import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Bitwise

/-!
# NEW proof: occurrence-aware finite face peeling

This reconstructs the missing finite combinatorial dependency of the recovered
`OccurrenceKasteleynDual` consumer. Literal dart multiplicities are retained.
A pivot is an edge of odd incidence in one remaining face and even incidence in
all other remaining faces. The actual finite candidate scan recursively removes
that face and sets its bit on return, without disturbing the other equations.

This module assumes neither a solved orientation nor a pivot order. The later
dual-connectivity consumer proves pivot existence from literal dual incidence.
No geometric face extraction or polynomial-time bit-cost bound is claimed here.
-/

namespace PlanarHom.MultiGraph.Kasteleyn
variable {F E : Type*}

/-- A directed traversal of a literal edge occurrence, with `true` forward. -/
abbrev Dart (E : Type*) := E × Bool

/-- One literal boundary dart list for each face label. -/
abbrev Boundaries (F E : Type*) := F → List (Dart E)

/-- Parity of the darts traversed opposite to the chosen edge orientation. -/
def boundaryParity (orientation : E → Bool) : List (Dart E) → Bool
  | [] => false
  | a :: ds => (orientation a.1 ^^ a.2) ^^ boundaryParity orientation ds

@[simp] theorem boundaryParity_cons (orientation : E → Bool) (a : Dart E) (ds : List (Dart E)) :
    boundaryParity orientation (a::ds) = ((orientation a.1 ^^ a.2) ^^ boundaryParity orientation ds) := rfl

/-- Clockwise oddness: disagreement parity is opposite to boundary-length parity. -/
def faceTarget (ds : List (Dart E)) : Bool := !ds.length.bodd

def FaceOdd (orientation : E → Bool) (ds : List (Dart E)) : Prop :=
  boundaryParity orientation ds = faceTarget ds

/-- The parity equation means that an odd number of literal traversals agree
with the chosen directions. This checks the geometric convention, rather than
merely proving an arbitrary Boolean linear system solvable. -/
theorem boundaryParity_agreementCount (orientation : E → Bool) (ds : List (Dart E)) :
    boundaryParity orientation ds =
      (ds.length.bodd ^^ (ds.countP (fun a => orientation a.1 == a.2)).bodd) := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [boundaryParity_cons,List.length_cons,Nat.bodd_succ,List.countP_cons,ih]
    cases orientation a.1 <;> cases a.2 <;>
      simp [Nat.bodd_succ]


/-- Exact conventional clockwise-odd interpretation, retaining every repeated dart. -/
theorem faceOdd_iff_odd_agreementCount (orientation : E → Bool) (ds : List (Dart E)) :
    FaceOdd orientation ds ↔ (ds.countP (fun a => orientation a.1 == a.2)).bodd = true := by
  unfold FaceOdd faceTarget
  rw [boundaryParity_agreementCount]
  cases ds.length.bodd <;> cases (ds.countP (fun a => orientation a.1 == a.2)).bodd <;> decide

variable [DecidableEq E]

/-- Occurrence parity counts every repeated traversal, irrespective of direction. -/
def incidenceParity (e : E) : List (Dart E) → Bool
  | [] => false
  | a :: ds => decide (a.1=e) ^^ incidenceParity e ds

/-- Reverse exactly one original edge occurrence. -/
def flip (orientation : E → Bool) (e : E) : E → Bool :=
  fun f => if f=e then !(orientation f) else orientation f

/-- The exact Boolean effect of reversing one occurrence, including repeats. -/
theorem boundaryParity_flip (orientation : E → Bool) (e : E) (ds : List (Dart E)) :
    boundaryParity (flip orientation e) ds =
      (boundaryParity orientation ds ^^ incidenceParity e ds) := by
  induction ds with
  | nil => rfl
  | cons a ds ih =>
    simp only [boundaryParity_cons,incidenceParity,ih]
    by_cases ha : a.1=e
    · simp only [flip,ha,if_pos,decide_true]
      cases orientation e <;> cases a.2 <;> cases boundaryParity orientation ds <;>
        cases incidenceParity e ds <;> rfl
    · simp only [flip,ha,decide_false,Bool.false_xor]
      exact (Bool.xor_assoc _ _ _).symm

/-- Odd incidence implies an actual occurrence in the finite candidate scan. -/
theorem exists_dart_of_incidenceParity {e : E} {ds : List (Dart E)}
    (h : incidenceParity e ds = true) : ∃ a ∈ ds, a.1=e := by
  induction ds with
  | nil => simp [incidenceParity] at h
  | cons a ds ih =>
    by_cases ha : a.1=e
    · exact ⟨a,List.mem_cons_self,ha⟩
    · have hh : incidenceParity e ds = true := by simpa [incidenceParity,ha] using h
      obtain ⟨b,hb,hbe⟩ := ih hh
      exact ⟨b,List.mem_cons_of_mem _ hb,hbe⟩

/-- Set one odd-incidence boundary equation by retaining or reversing its pivot. -/
def repairFace (ds : List (Dart E)) (e : E) (orientation : E → Bool) : E → Bool :=
  if boundaryParity orientation ds = faceTarget ds then orientation else flip orientation e

theorem repairFace_correct (ds : List (Dart E)) (e : E) (orientation : E → Bool)
    (he : incidenceParity e ds = true) : FaceOdd (repairFace ds e orientation) ds := by
  unfold repairFace
  split_ifs with h
  · exact h
  · unfold FaceOdd
    rw [boundaryParity_flip,he]
    cases hb : boundaryParity orientation ds <;> cases ht : faceTarget ds <;>
      simp_all

theorem repairFace_preserves (ds xs : List (Dart E)) (e : E) (orientation : E → Bool)
    (he : incidenceParity e xs = false) :
    boundaryParity (repairFace ds e orientation) xs = boundaryParity orientation xs := by
  unfold repairFace
  split_ifs
  · rfl
  · rw [boundaryParity_flip,he,Bool.xor_false]

variable [DecidableEq F]

/-- A pivot is exclusive among the remaining equations, at the level of parity. -/
def HasPivot (boundary : Boundaries F E) (fs : List F) : Prop :=
  ∃ f ∈ fs, ∃ e, incidenceParity e (boundary f) = true ∧
    ∀ g ∈ fs, g ≠ f → incidenceParity e (boundary g) = false

/-- Every nonempty remaining sublist has an exclusive pivot. -/
def Peelable (boundary : Boundaries F E) (fs : List F) : Prop :=
  ∀ us : List F, (∀ f, f ∈ us → f ∈ fs) → us ≠ [] → HasPivot boundary us

/-- Actual finite scan space; repeated darts and repeated edge labels are harmless. -/
def pivotCandidates (boundary : Boundaries F E) (fs : List F) : List (F × E) :=
  fs.flatMap (fun f => (boundary f).map (fun a => (f,a.1)))

def pivotTest (boundary : Boundaries F E) (fs : List F) (p : F × E) : Bool :=
  incidenceParity p.2 (boundary p.1) &&
    fs.all (fun g => decide (g=p.1) || !incidenceParity p.2 (boundary g))

def pickPivot (boundary : Boundaries F E) (fs : List F) : Option (F × E) :=
  (pivotCandidates boundary fs).find? (pivotTest boundary fs)

theorem pivotTest_iff (boundary : Boundaries F E) (fs : List F) (p : F × E) :
    pivotTest boundary fs p = true ↔
      incidenceParity p.2 (boundary p.1) = true ∧
      ∀ g ∈ fs, g ≠ p.1 → incidenceParity p.2 (boundary g) = false := by
  simp only [pivotTest,Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,
    decide_eq_true_eq,Bool.not_eq_true']
  constructor
  · rintro ⟨he,hg⟩
    exact ⟨he,fun g hmem hne => (hg g hmem).resolve_left hne⟩
  · rintro ⟨he,hg⟩
    refine ⟨he,fun g hmem => ?_⟩
    by_cases h : g=p.1
    · exact Or.inl h
    · exact Or.inr (hg g hmem h)

theorem pickPivot_sound (boundary : Boundaries F E) (fs : List F) {p : F × E}
    (h : pickPivot boundary fs = some p) :
    p.1 ∈ fs ∧ incidenceParity p.2 (boundary p.1) = true ∧
      ∀ g ∈ fs, g ≠ p.1 → incidenceParity p.2 (boundary g) = false := by
  have htest := (pivotTest_iff boundary fs p).mp (List.find?_some h)
  have hmem := List.mem_of_find?_eq_some h
  change p ∈ pivotCandidates boundary fs at hmem
  obtain ⟨f,hf,hmap⟩ := List.mem_flatMap.mp hmem
  obtain ⟨a,ha,hp⟩ := List.mem_map.mp hmap
  have hfp : f=p.1 := congrArg Prod.fst hp
  exact ⟨hfp ▸ hf,htest⟩

theorem pickPivot_exists (boundary : Boundaries F E) (fs : List F) (h : HasPivot boundary fs) :
    ∃ p, pickPivot boundary fs = some p := by
  obtain ⟨f,hf,e,he,hrest⟩ := h
  obtain ⟨a,ha,hae⟩ := exists_dart_of_incidenceParity he
  have hcandidate : (f,e) ∈ pivotCandidates boundary fs := by
    apply List.mem_flatMap.mpr
    refine ⟨f,hf,?_⟩
    exact List.mem_map.mpr ⟨a,ha,Prod.ext rfl hae⟩
  have htest : pivotTest boundary fs (f,e) = true :=
    (pivotTest_iff boundary fs (f,e)).mpr ⟨he,hrest⟩
  cases hp : pickPivot boundary fs with
  | some p => exact ⟨p,rfl⟩
  | none =>
    exact ((List.find?_eq_none.mp hp) (f,e) hcandidate htest).elim

/-- Computed reverse substitution: solve residual faces, then repair the selected
face. One fuel unit is consumed per erased face. -/
def orientAux (boundary : Boundaries F E) : Nat → List F → (E → Bool) → E → Bool
  | 0, _, initial => initial
  | n+1, fs, initial =>
    match pickPivot boundary fs with
    | none => initial
    | some p => repairFace (boundary p.1) p.2 (orientAux boundary n (fs.erase p.1) initial)

/-- Exact correctness of the actual recursion, with the explicit finite clock. -/
theorem orientAux_correct (boundary : Boundaries F E) (n : Nat) (fs : List F)
    (hn : fs.Nodup) (hp : Peelable boundary fs) (hlen : fs.length ≤ n) (initial : E → Bool) :
    ∀ f ∈ fs, FaceOdd (orientAux boundary n fs initial) (boundary f) := by
  induction n generalizing fs with
  | zero =>
    have hfs : fs = [] := List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero hlen)
    simp [hfs]
  | succ n ih =>
    by_cases hempty : fs=[]
    · simp [hempty]
    obtain ⟨p,hpick⟩ := pickPivot_exists boundary fs (hp fs (fun _ h => h) hempty)
    obtain ⟨hpf,hodd,heven⟩ := pickPivot_sound boundary fs hpick
    have hp' : Peelable boundary (fs.erase p.1) := by
      intro us hsub hne
      exact hp us (fun g hg => List.erase_subset (hsub g hg)) hne
    have hlen' : (fs.erase p.1).length ≤ n := by
      rw [List.length_erase_of_mem hpf]
      have hpos : 0 < fs.length := List.length_pos_iff.mpr hempty
      omega
    have hres := ih (fs.erase p.1) (hn.erase p.1) hp' hlen'
    intro f hf
    simp only [orientAux,hpick]
    by_cases heq : f=p.1
    · subst f
      exact repairFace_correct _ _ _ hodd
    · unfold FaceOdd
      rw [repairFace_preserves _ _ _ _ (heven f hf heq)]
      exact hres f ((List.mem_erase_of_ne heq).mpr hf)

/-- The executable finite face solver uses exactly the boundary-row count as fuel. -/
def orientFaces (boundary : Boundaries F E) (fs : List F) (initial : E → Bool) : E → Bool :=
  orientAux boundary fs.length fs initial

/-- Every listed face is clockwise odd under the orientation actually computed
by finite pivot scanning and reverse substitution. -/
theorem orientFaces_correct (boundary : Boundaries F E) (fs : List F)
    (hn : fs.Nodup) (hp : Peelable boundary fs) (initial : E → Bool) :
    ∀ f ∈ fs, FaceOdd (orientFaces boundary fs initial) (boundary f) :=
  orientAux_correct boundary fs.length fs hn hp le_rfl initial

end PlanarHom.MultiGraph.Kasteleyn
