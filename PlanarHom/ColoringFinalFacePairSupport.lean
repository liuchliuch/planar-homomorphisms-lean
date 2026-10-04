import PlanarHom.ColoringFinalFacePairs

/-! Exact support of the canonical nested face-splice loop. Local disjoint
marker families imply a globally nonrepeating list, with no unproved loop bound. -/
noncomputable section
open Classical
namespace PlanarHom.ColoringEmitter.FramedCanvas
open MultiGraph MultiGraph.Kasteleyn PlanarityLRRealization FinitePermutationCycles
open PositiveBlockProgram ParsimoniousNorOneInThree

 theorem prefixPairs_mem (f : NumericFormula) (hf : NumericValid f) (n : ℕ) (p : Dart f×Dart f) :
    p∈prefixPairs f hf n ↔ ∃i : Canvas.Index f,i.val<n ∧ p∈cellPairs f hf i := by
  induction n with
  | zero => simp [prefixPairs]
  | succ n ih =>
      by_cases hn : n<(canvas f).length
      · simp only [prefixPairs,dif_pos hn,List.mem_append,ih]
        constructor
        · rintro (⟨i,hi,hp⟩ | hp)
          · exact ⟨i,by omega,hp⟩
          · exact ⟨⟨n,hn⟩,Nat.lt_succ_self n,hp⟩
        · rintro ⟨i,hi,hp⟩
          by_cases he : i.val=n
          · right
            have hie : i=⟨n,hn⟩ := Fin.ext he
            simpa only [hie] using hp
          · exact Or.inl ⟨i,by omega,hp⟩
      · simp only [prefixPairs,dif_neg hn,ih]
        constructor
        · rintro ⟨i,hi,hp⟩; exact ⟨i,by omega,hp⟩
        · rintro ⟨i,hi,hp⟩; exact ⟨i,by have := i.isLt; omega,hp⟩

 theorem prefixMarkers_mem (f : NumericFormula) (hf : NumericValid f) (n : ℕ) (a : Dart f) :
    a∈pairMarkers (prefixPairs f hf n) ↔
      ∃i : Canvas.Index f,i.val<n ∧ a∈pairMarkers (cellPairs f hf i) := by
  simp only [pairMarkers,List.mem_flatMap,prefixPairs_mem]
  constructor
  · rintro ⟨p,⟨i,hi,hp⟩,ha⟩
    exact ⟨i,hi,p,hp,ha⟩
  · rintro ⟨i,hi,p,hp,ha⟩
    exact ⟨p,⟨i,hi,hp⟩,ha⟩

 theorem prefixMarkers_nodup (f : NumericFormula) (hf : NumericValid f)
    (hl : ∀i : Canvas.Index f,(pairMarkers (cellPairs f hf i)).Nodup)
    (hd : ∀i j : Canvas.Index f,i≠j→List.Disjoint (pairMarkers (cellPairs f hf i))
      (pairMarkers (cellPairs f hf j))) (n : ℕ) :
    (pairMarkers (prefixPairs f hf n)).Nodup := by
  induction n with
  | zero => simp [prefixPairs]
  | succ n ih =>
      by_cases hn : n<(canvas f).length
      · simp only [prefixPairs,dif_pos hn,pairMarkers,List.flatMap_append]
        apply List.nodup_append.mpr
        refine ⟨ih,hl ⟨n,hn⟩,?_⟩
        intro a ha b hb he
        subst b
        obtain ⟨i,hi,hp⟩ := (prefixMarkers_mem f hf n a).mp ha
        exact hd i ⟨n,hn⟩ (by intro hh; have hv := congrArg Fin.val hh; simp only at hv; omega) hp hb
      · simpa only [prefixPairs,dif_neg hn] using ih

 theorem finalMarkers_nodup (f : NumericFormula) (hf : NumericValid f)
    (hl : ∀i : Canvas.Index f,(pairMarkers (cellPairs f hf i)).Nodup)
    (hd : ∀i j : Canvas.Index f,i≠j→List.Disjoint (pairMarkers (cellPairs f hf i))
      (pairMarkers (cellPairs f hf j))) :
    (pairMarkers (finalPairs f hf)).Nodup := prefixMarkers_nodup f hf hl hd _

 theorem finalPairs_mem (f : NumericFormula) (hf : NumericValid f) (p : Dart f×Dart f) :
    p∈finalPairs f hf ↔ ∃i : Canvas.Index f,p∈cellPairs f hf i := by
  rw [finalPairs,prefixPairs_mem]
  constructor
  · rintro ⟨i,_,hp⟩; exact ⟨i,hp⟩
  · rintro ⟨i,hp⟩; exact ⟨i,i.isLt,hp⟩
end PlanarHom.ColoringEmitter.FramedCanvas
