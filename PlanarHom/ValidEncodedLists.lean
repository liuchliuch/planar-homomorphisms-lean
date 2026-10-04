import PlanarHom.ValidEncodedWords

/-! Exact decomposition of every successfully decoded raw list, preserving
noncanonical item words and the original binary count header. -/
namespace PlanarHom.Complexity.BitEncoding.ValidWord

private theorem exists_validWords {α : Type} (e : BitEncoding α)
    (words : List Bits) (xs : List α) (h : words.mapM e.decode=some xs) :
    ∃items : List (ValidWord e),items.map raw=words ∧ items.map value=xs:=by
  induction words generalizing xs with
  | nil=>simp at h; subst xs; exact ⟨[],rfl,rfl⟩
  | cons w words ih=>
    cases hw:e.decode w with
    | none=>simp [List.mapM_cons,hw] at h
    | some x=>
      cases ht:words.mapM e.decode with
      | none=>simp [List.mapM_cons,hw,ht] at h
      | some ys=>
        have hx : x::ys=xs:=by simpa [List.mapM_cons,hw,ht] using h
        subst xs
        obtain ⟨tail,hraw,hvalue⟩:=ih ys ht
        let head : ValidWord e:=⟨w,⟨x,hw⟩⟩
        refine ⟨head::tail,?_,?_⟩
        · simpa [head,raw] using congrArg (List.cons w) hraw
        · have hv : head.value=x:=value_eq hw
          simp [hv,hvalue]

structure ListParts {α : Type} (e : BitEncoding α) (w : ValidWord e.list) where
  header : Bits
  items : List (ValidWord e)
  raw_eq : w.raw=frame header++frames (items.map raw)
  count_eq : Computability.decodeNat header=items.length
  value_eq : w.value=items.map value

private theorem nonempty_listParts {α : Type} (e : BitEncoding α) (w : ValidWord e.list) :
    Nonempty (ListParts e w):=by
  obtain ⟨xs,hs⟩:=w.property
  change e.list.decode w.raw=some xs at hs
  cases hu:unframe w.raw with
  | none=>simp [-decode_raw,list,hu] at hs
  | some p=>
    rcases p with ⟨header,rest⟩
    cases hr:unframes (Computability.decodeNat header) rest with
    | none=>simp [-decode_raw,list,nat,hu,hr] at hs
    | some p=>
      rcases p with ⟨words,tail⟩
      by_cases ht:tail=[]
      · subst tail
        have hm : words.mapM e.decode=some xs:=by simpa [-decode_raw,list,nat,hu,hr] using hs
        obtain ⟨items,hraw,hvalue⟩:=exists_validWords e words xs hm
        obtain ⟨hlen,hrest⟩:=unframes_spec _ _ _ _ hr
        refine ⟨⟨header,items,?_,?_,?_⟩⟩
        · rw [unframe_spec _ _ _ hu,hrest,hraw,List.append_nil]
        · have hl:=congrArg List.length hraw
          simp only [List.length_map] at hl
          omega
        · exact (value_eq hs).trans hvalue.symm
      · simp [-decode_raw,list,nat,hu,hr,ht] at hs

noncomputable def listParts {α : Type} (e : BitEncoding α) (w : ValidWord e.list) :
    ListParts e w:=Classical.choice (nonempty_listParts e w)

end PlanarHom.Complexity.BitEncoding.ValidWord
