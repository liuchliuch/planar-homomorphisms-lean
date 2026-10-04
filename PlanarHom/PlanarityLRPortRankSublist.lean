import PlanarHom.PlanarityLRNonalternatingRankForce
import Mathlib.Data.List.Nodup

/-! NEW exact conversion of the proved four-dart word nonalternation into
rank nonalternation. All four original labels must occur in the literal word. -/
namespace PlanarHom.PlanarityLRNecessity

theorem four_sublist_of_idxOf_lt {A : Type*} [DecidableEq A] (xs : List A)
    (a b c d : A) (ha : a∈xs) (hb : b∈xs) (hc : c∈xs) (hd : d∈xs)
    (hab : xs.idxOf a<xs.idxOf b) (hbc : xs.idxOf b<xs.idxOf c) (hcd : xs.idxOf c<xs.idxOf d) :
    [a,b,c,d].Sublist xs := by
  let i : Fin xs.length := ⟨xs.idxOf a,List.idxOf_lt_length_iff.mpr ha⟩
  let j : Fin xs.length := ⟨xs.idxOf b,List.idxOf_lt_length_iff.mpr hb⟩
  let k : Fin xs.length := ⟨xs.idxOf c,List.idxOf_lt_length_iff.mpr hc⟩
  let l : Fin xs.length := ⟨xs.idxOf d,List.idxOf_lt_length_iff.mpr hd⟩
  have hsort : [i,j,k,l].Pairwise (·<·) := by
    simp [List.pairwise_cons,i,j,k,l,hab,hbc,hcd,hab.trans hbc,hbc.trans hcd,(hab.trans hbc).trans hcd]
  have hs := List.map_getElem_sublist hsort
  change [xs[i.val],xs[j.val],xs[k.val],xs[l.val]].Sublist xs at hs
  simpa only [i,j,k,l,List.getElem_idxOf] using hs

theorem idxOf_ne_of_mem_ne {A : Type*} [DecidableEq A] (xs : List A) {a b : A}
    (ha : a∈xs) (hb : b∈xs) (hne : a≠b) : xs.idxOf a≠xs.idxOf b := by
  intro he
  have hga := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr ha)
  have hgb := List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hb)
  apply hne
  exact hga.symm.trans (by simpa only [he] using hgb)

theorem pairNonalternating_of_word {E : Type*} [DecidableEq E] (word : List (E×Bool))
    (hword : ∀ a b : E×Bool, a.1≠b.1 → ¬[a,b,(a.1,!a.2),(b.1,!b.2)].Sublist word)
    (b c : E) (hne : b≠c) (hb : ∀ s, (b,s)∈word) (hc : ∀ s, (c,s)∈word) :
    PairNonalternating word.idxOf b c := by
  intro s t
  constructor
  · rintro ⟨h₁,h₂,h₃⟩
    exact hword (b,s) (c,t) hne (four_sublist_of_idxOf_lt word _ _ _ _ (hb s) (hc t) (hb (!s)) (hc (!t))
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₁)
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₂)
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₃))
  · rintro ⟨h₁,h₂,h₃⟩
    exact hword (c,t) (b,s) hne.symm (four_sublist_of_idxOf_lt word _ _ _ _ (hc t) (hb s) (hc (!t)) (hb (!s))
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₁)
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₂)
      (by simpa only [List.idxOf,Lean.Grind.beq_eq_decide_eq] using h₃))

end PlanarHom.PlanarityLRNecessity
