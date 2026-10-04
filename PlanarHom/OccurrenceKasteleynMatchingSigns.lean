import PlanarHom.OccurrenceKasteleynWordSigns
import PlanarHom.OccurrenceKasteleynDartWords
/-! NEW reconstruction, using recovered matching-sign proof fragments.
The formerly missing word-sign foundation is derived from literal pair exchange. -/
noncomputable section
open Classical
open scoped BigOperators
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [LinearOrder V]
local instance (priority := high) : DecidableEq (V × V) := Classical.decEq (V × V)
/-- Pair normalization forgets direction, while retaining its occurrence label. -/
theorem normalize_dartPair (G : MultiGraph V E) (d : Dart E) :
    normalizePair (G.dartPair d) = G.canonicalPair d.1 := by
  cases h : d.2 <;> simp [dartPair,h,normalizePair,canonicalPair,min_comm,max_comm]

/-- Canonical and directed occurrence signs differ by exactly endpoint order. -/
theorem canonicalSign_eq_dartSign (G : MultiGraph V E) (orientation : E → Bool)
    (d : Dart E) (hne : (G.dartPair d).1 ≠ (G.dartPair d).2) :
    G.canonicalSign (R := ℤ) orientation d.1 =
      orderSign (G.dartPair d).1 (G.dartPair d).2 * dartSign orientation d := by
  cases hd : d.2 <;> simp only [dartPair,hd,Bool.false_eq_true,if_false,if_true] at hne ⊢
  · rcases lt_or_gt_of_ne hne with h | h <;>
      cases ho : orientation d.1 <;> simp [canonicalSign,orderSign,endpointOrderSign,orientationSign,dartSign,hd,ho,h,not_lt_of_gt h]
  · by_cases h : G.src d.1 < G.dst d.1 <;> cases ho : orientation d.1 <;> simp [canonicalSign,orderSign,endpointOrderSign,orientationSign,dartSign,hd,ho,h]

/-- The original occurrence-perfect-matching sign equals the actual directed
word sign times its dart product. This applies to any partial matching list
whose endpoint word is distinct, without a nonzero-weight assumption. -/
theorem matchingPfaffianSign_eq_word (G : MultiGraph V E) (orientation : E → Bool)
    (ds : List (Dart E)) (hn : (G.dartWord ds).Nodup) :
    G.matchingPfaffianSign (R := ℤ) orientation (dartEdges ds) =
      wordSign (G.dartWord ds) * boundarySign orientation ds := by
  have hpair : (dartEdges ds).image G.canonicalPair =
      ((ds.map G.dartPair).map normalizePair).toFinset := by
    ext p
    simp [dartEdges,List.map_map,Function.comp_def,G.normalize_dartPair]
  have hs : pairingSign ((ds.map G.dartPair).map normalizePair).toFinset =
      wordSign (pairWord (ds.map G.dartPair)) *
        ((ds.map G.dartPair).map (fun p => orderSign p.1 p.2)).prod := by
    convert pairingSign_normalize_eq_wordSign (ds.map G.dartPair) hn using 1
    congr 1
    ext p
    simp
  have hp : (∏ e ∈ dartEdges ds, G.canonicalSign (R := ℤ) orientation e) =
      (ds.map (fun d => G.canonicalSign (R := ℤ) orientation d.1)).prod := by
    rw [dartEdges,List.prod_toFinset _ (G.dartEdges_nodup ds hn)]
    simp [List.map_map,Function.comp_def]
  have ht : (ds.map (fun d => G.canonicalSign (R := ℤ) orientation d.1)).prod =
      (ds.map (fun d => orderSign (G.dartPair d).1 (G.dartPair d).2)).prod * boundarySign orientation ds := by
    unfold boundarySign
    rw [← List.prod_map_mul]
    apply congrArg List.prod
    apply List.map_congr_left
    intro d hd
    exact G.canonicalSign_eq_dartSign orientation d (G.dartPair_ne ds hn d hd)
  have hsq : (ds.map (fun d => orderSign (G.dartPair d).1 (G.dartPair d).2)).prod ^ 2 = 1 := by
    have hs : ∀ xs : List (Dart E),
        (xs.map (fun d => orderSign (G.dartPair d).1 (G.dartPair d).2)).prod ^ 2 = 1 := by
      intro xs
      induction xs with
      | nil => rfl
      | cons d xs ih => simp only [List.map_cons,List.prod_cons,mul_pow,orderSign_sq,ih,mul_one]
    exact hs ds
  simp only [matchingPfaffianSign,Int.cast_id]
  rw [hpair,hp,hs,ht]
  simp only [List.map_map,Function.comp_def]
  calc
    _ = wordSign (pairWord (List.map G.dartPair ds)) *
        (ds.map (fun d=>orderSign (G.dartPair d).1 (G.dartPair d).2)).prod ^ 2 *
        boundarySign orientation ds := by ring
    _ = _ := by rw [hsq]; simp [dartWord]

/-- Literal word data for an alternating occurrence cycle. -/
structure CycleFlipWordData (G : MultiGraph V E) (M N : Finset E) where
  left : List (Dart E)
  right : List (Dart E)
  common : List (Dart E)
  first : V
  rest : List V
  left_word : G.dartWord left = first :: rest
  right_word : G.dartWord right = rest ++ [first]
  left_nodup : (G.dartWord (left ++ common)).Nodup
  right_nodup : (G.dartWord (right ++ common)).Nodup
  left_edges : dartEdges (left ++ common) = M
  right_edges : dartEdges (right ++ common) = N

theorem CycleFlipWordData.sign_eq {G : MultiGraph V E} {M N : Finset E}
    (c : CycleFlipWordData G M N) (orientation : E → Bool)
    (hodd : boundarySign orientation (c.left ++ c.right) = -1) :
    G.matchingPfaffianSign (R := ℤ) orientation M = G.matchingPfaffianSign orientation N := by
  have hw := orientedPairSign_rotate_word (c.left.map G.dartPair) (c.right.map G.dartPair)
    (c.common.map G.dartPair) c.first c.rest c.left_word c.right_word
    (by simpa [dartWord] using c.left_nodup)
  have hleft := G.matchingPfaffianSign_eq_word orientation _ c.left_nodup
  have hright := G.matchingPfaffianSign_eq_word orientation _ c.right_nodup
  rw [c.left_edges] at hleft
  rw [c.right_edges] at hright
  rw [hleft,hright]
  simp only [dartWord,List.map_append,wordSign_pairWord,boundarySign_append]
  rw [hw]
  rw [boundarySign_append] at hodd
  have hr := boundarySign_sq orientation c.right
  have hs : boundarySign orientation c.left = -boundarySign orientation c.right := by
    calc
      _ = boundarySign orientation c.left * (boundarySign orientation c.right)^2 := by rw [hr,mul_one]
      _ = (boundarySign orientation c.left * boundarySign orientation c.right) *
          boundarySign orientation c.right := by ring
      _ = _ := by rw [hodd]; ring
  rw [hs]
  ring

end PlanarHom.MultiGraph
