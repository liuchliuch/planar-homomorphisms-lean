import PlanarHom.OccurrenceKasteleynDual
import PlanarHom.OccurrenceKasteleynOrientationLog

/-!
# NEW proof: materialized finite-face orientation logs

This supplies the recovered consumer's final `computeOrientation_faceOdd` API
with a proved, executable table-to-toggle-log program. It is new implementation,
not the incomplete historical PeelingSemantics source fragment. No TM2 polynomial
bit-cost theorem or effective planar embedding extraction is claimed here.
-/
namespace PlanarHom.MultiGraph.Kasteleyn

/-- A materialized labelled boundary row. -/
abbrev RawFace := Nat × List (Dart Nat)

def faceTable (boundary : Boundaries Nat Nat) (fs : List Nat) : List RawFace :=
  fs.map (fun f => (f,boundary f))

/-- The stored first row for a label; absent labels get the empty boundary. -/
def tableBoundary (table : List RawFace) : Boundaries Nat Nat :=
  fun f => (table.lookup f).getD []

/-- Duplicate labels in a freshly materialized table have the same literal row. -/
theorem tableBoundary_faceTable (boundary : Boundaries Nat Nat) (fs : List Nat)
    {f : Nat} (hf : f ∈ fs) : tableBoundary (faceTable boundary fs) f = boundary f := by
  induction fs with
  | nil => simp at hf
  | cons g fs ih =>
    by_cases h : f=g
    · simp [tableBoundary,faceTable,h]
    · have hmem : f ∈ fs := (List.mem_cons.mp hf).resolve_left h
      have hbeq : (f == g) = false := beq_eq_false_iff_ne.mpr h
      simpa [tableBoundary,faceTable,List.lookup_cons,hbeq] using ih hmem

private theorem all_congr_on {A : Type*} (xs : List A) (p q : A → Bool)
    (h : ∀ a ∈ xs, p a=q a) : xs.all p = xs.all q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.all_cons,h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

private theorem find_congr_on {A : Type*} (xs : List A) (p q : A → Bool)
    (h : ∀ a ∈ xs, p a=q a) : xs.find? p = xs.find? q := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.find?_cons,h a List.mem_cons_self,
      ih (fun x hx => h x (List.mem_cons_of_mem _ hx))]

variable {F E : Type*} [DecidableEq F] [DecidableEq E]

/-- Only the boundary rows actually listed in the scan can affect its choice. -/
theorem pickPivot_boundary_congr (b c : Boundaries F E) (fs : List F)
    (h : ∀ f ∈ fs, b f=c f) : pickPivot b fs = pickPivot c fs := by
  have hscan : pivotCandidates b fs = pivotCandidates c fs := by
    unfold pivotCandidates
    induction fs with
    | nil => rfl
    | cons f fs ih =>
      simp only [List.flatMap_cons,h f List.mem_cons_self,
        ih (fun g hg => h g (List.mem_cons_of_mem _ hg))]
  unfold pickPivot
  rw [hscan]
  apply find_congr_on
  intro p hp
  obtain ⟨f,hf,ha⟩ := List.mem_flatMap.mp hp
  obtain ⟨a,_,ha⟩ := List.mem_map.mp ha
  have hfp : f=p.1 := congrArg Prod.fst ha
  have hpfs : p.1 ∈ fs := hfp ▸ hf
  unfold pivotTest
  rw [h p.1 hpfs]
  congr 1
  apply all_congr_on
  intro g hg
  rw [h g hg]

/-- Restricting or materializing a boundary function preserves the exact computed
orientation whenever all listed literal boundary rows agree. -/
theorem orientAux_boundary_congr (b c : Boundaries F E) (n : Nat) (fs : List F)
    (h : ∀ f ∈ fs, b f=c f) (initial : E → Bool) :
    orientAux b n fs initial = orientAux c n fs initial := by
  induction n generalizing fs with
  | zero => rfl
  | succ n ih =>
    simp only [orientAux,pickPivot_boundary_congr b c fs h]
    cases hp : pickPivot c fs with
    | none => rfl
    | some p =>
      have hmem := (pickPivot_sound c fs hp).1
      simp only
      rw [h p.1 hmem,ih (fs.erase p.1) (fun f hf => h f (List.erase_subset hf))]

/-- A materialized toggle-log implementation of the same reverse substitution. -/
def orientLogAux (boundary : Boundaries Nat Nat) : Nat → List Nat → List Nat
  | 0, _ => []
  | n+1, fs =>
    match pickPivot boundary fs with
    | none => []
    | some p =>
      let log := orientLogAux boundary n (fs.erase p.1)
      if boundaryParity (logOrientation log) (boundary p.1) = faceTarget (boundary p.1)
      then log else p.2 :: log

/-- One stored toggle is exactly one occurrence reversal. -/
theorem logOrientation_cons_eq_flip (e : Nat) (log : List Nat) :
    logOrientation (e::log) = flip (logOrientation log) e := by
  funext f
  simp only [logOrientation_cons,flip]
  by_cases h : e=f
  · simp [h]
  · simp [h,Ne.symm h]

/-- Exact semantic equality with the proved finite face solver. -/
theorem orientLogAux_semantics (boundary : Boundaries Nat Nat) (n : Nat) (fs : List Nat) :
    logOrientation (orientLogAux boundary n fs) = orientAux boundary n fs (fun _ => true) := by
  induction n generalizing fs with
  | zero => rfl
  | succ n ih =>
    simp only [orientLogAux,orientAux]
    cases hp : pickPivot boundary fs with
    | none => rfl
    | some p =>
      simp only
      unfold repairFace
      rw [← ih (fs.erase p.1)]
      split_ifs
      · rfl
      · exact logOrientation_cons_eq_flip p.2 _

/-- The actual finite table-to-log function, including empty/malformed tables. -/
def computeOrientation (table : List RawFace) : List Nat :=
  orientLogAux (tableBoundary table) table.length (table.map Prod.fst)

/-- Materialization changes neither the exact orientation bits nor the clock. -/
theorem computeOrientation_semantics (boundary : Boundaries Nat Nat) (fs : List Nat)
    (_hn : fs.Nodup) :
    logOrientation (computeOrientation (faceTable boundary fs)) =
      orientFaces boundary fs (fun _ => true) := by
  unfold computeOrientation
  simp only [faceTable,List.length_map,List.map_map,Function.comp_def]
  change logOrientation (orientLogAux (tableBoundary (faceTable boundary fs)) fs.length
    (fs.map id)) = _
  rw [List.map_id,orientLogAux_semantics]
  exact orientAux_boundary_congr _ _ _ _
    (fun f hf => tableBoundary_faceTable boundary fs hf) _

/-- Exact recovered endpoint signature: the program's actual returned log makes
every listed non-exterior face clockwise odd on compatible reachable dual data. -/
theorem computeOrientation_faceOdd (D : DualIncidence Nat Nat)
    (boundary : Boundaries Nat Nat) (hc : D.Compatible boundary)
    (root : Nat) (fs : List Nat)
    (hconn : ∀ f ∈ fs, Relation.ReflTransGen D.Adj root f)
    (hn : fs.Nodup) (hr : root ∉ fs) :
    ∀ f ∈ fs, FaceOdd (logOrientation (computeOrientation (faceTable boundary fs))) (boundary f) := by
  rw [computeOrientation_semantics boundary fs hn]
  exact orientFaces_correct boundary fs hn
    (D.peelable_of_reachable boundary hc root fs hconn hr) (fun _ => true)

end PlanarHom.MultiGraph.Kasteleyn
