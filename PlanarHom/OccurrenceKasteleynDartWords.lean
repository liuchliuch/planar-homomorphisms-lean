import PlanarHom.OccurrenceKasteleynWordBase
import PlanarHom.OccurrenceKasteleynBoundarySigns
import PlanarHom.PlanarityLRRealizationGermPieces
noncomputable section
open Classical
namespace PlanarHom.MultiGraph
open Kasteleyn
variable {V E : Type*} [LinearOrder V]
/-- Endpoint word for a list of independent selected occurrence darts. -/
def dartWord (G : MultiGraph V E) (ds : List (Dart E)) : List V :=
  pairWord (ds.map G.dartPair)

/-- The literal selected occurrence set; no endpoint pairs are identified. -/
def dartEdges (ds : List (Dart E)) : Finset E := (ds.map Prod.fst).toFinset

@[simp] theorem dartWord_nil (G : MultiGraph V E) : G.dartWord [] = [] := rfl

@[simp] theorem dartWord_cons (G : MultiGraph V E) (d : Dart E) (ds : List (Dart E)) :
    G.dartWord (d :: ds) = (G.dartPair d).1 :: (G.dartPair d).2 :: G.dartWord ds := rfl

@[simp] theorem dartWord_append (G : MultiGraph V E) (ds es : List (Dart E)) :
    G.dartWord (ds ++ es) = G.dartWord ds ++ G.dartWord es := by
  simp [dartWord,pairWord,List.flatMap_append]

@[simp] theorem dartWord_length (G : MultiGraph V E) (ds : List (Dart E)) :
    (G.dartWord ds).length = 2 * ds.length := by simp [dartWord]

theorem src_mem_dartWord (G : MultiGraph V E) {d : Dart E} {ds : List (Dart E)}
    (hd : d ∈ ds) : G.src d.1 ∈ G.dartWord ds := by
  have hm : G.dartPair d ∈ ds.map G.dartPair := List.mem_map.mpr ⟨d,hd,rfl⟩
  cases h : d.2
  · simpa [dartPair,h] using snd_mem_pairWord hm
  · simpa [dartPair,h] using fst_mem_pairWord hm

/-- Distinct endpoint words exclude loops and repeated use of one occurrence. -/
theorem dartEdges_nodup (G : MultiGraph V E) (ds : List (Dart E))
    (hn : (G.dartWord ds).Nodup) : (ds.map Prod.fst).Nodup := by
  induction ds with
  | nil => simp
  | cons d ds ih =>
    change ((G.dartPair d).1 :: (G.dartPair d).2 :: G.dartWord ds).Nodup at hn
    have hn₁ := List.nodup_cons.mp hn
    have hn₂ := List.nodup_cons.mp hn₁.2
    apply List.nodup_cons.mpr
    refine ⟨?_,ih hn₂.2⟩
    intro hm
    obtain ⟨e,he,hed⟩ := List.mem_map.mp hm
    have hs : G.src d.1 ∈ G.dartWord ds := hed ▸ G.src_mem_dartWord he
    cases hd : d.2
    · exact hn₂.1 (by simpa [dartPair,hd] using hs)
    · exact hn₁.1 (List.mem_cons_of_mem _ (by simpa [dartPair,hd] using hs))

theorem dartPair_ne (G : MultiGraph V E) (ds : List (Dart E))
    (hn : (G.dartWord ds).Nodup) (d : Dart E) (hd : d ∈ ds) :
    (G.dartPair d).1 ≠ (G.dartPair d).2 := by
  have hm : G.dartPair d ∈ ds.map G.dartPair := List.mem_map.mpr ⟨d,hd,rfl⟩
  have h := (List.nodup_flatMap.mp hn).1 _ hm
  simpa using h


end PlanarHom.MultiGraph
