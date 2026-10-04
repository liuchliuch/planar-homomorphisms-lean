import PlanarHom.CodecSizeBounds
import Mathlib.Data.Num.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Linear canonical-code size bounds on every successful raw decoding.
The natural decoder may add a high `true` to a noncanonical input; no identity
between that decoder and ordinary padded binary value is assumed. -/

namespace PlanarHom.Complexity
namespace BitEncoding

/-- Successful frame parsing consumes precisely one complete escaped prefix. -/
theorem unframe_spec (s w t : Bits) (h : unframe s=some (w,t)) : s=frame w++t := by
  induction s using List.twoStepInduction generalizing w t with
  | nil => simp [unframe] at h
  | singleton b =>
    cases b with
    | false => simp [unframe] at h; rcases h with ⟨rfl,rfl⟩; rfl
    | true => simp [unframe] at h
  | cons_cons a b bs ih _ =>
    cases a with
    | false => simp [unframe] at h; rcases h with ⟨rfl,rfl⟩; rfl
    | true =>
      cases hu:unframe bs with
      | none => simp [unframe,hu] at h
      | some p =>
        rcases p with ⟨u,v⟩
        simp [unframe,hu] at h
        rcases h with ⟨rfl,rfl⟩
        rw [ih _ _ hu]
        rfl

theorem unframes_spec (n : ℕ) (s : Bits) (ws : List Bits) (tail : Bits)
    (h : unframes n s=some (ws,tail)) : ws.length=n ∧ s=frames ws++tail := by
  induction n generalizing s ws tail with
  | zero => simp [unframes] at h; rcases h with ⟨rfl,rfl⟩; exact ⟨rfl,rfl⟩
  | succ n ih =>
    cases hu:unframe s with
    | none => simp [unframes,hu] at h
    | some p =>
      rcases p with ⟨w,rest⟩
      cases hv:unframes n rest with
      | none => simp [unframes,hu,hv] at h
      | some p =>
        rcases p with ⟨words,final⟩
        simp [unframes,hu,hv] at h
        rcases h with ⟨rfl,rfl⟩
        obtain ⟨hl,hs⟩:=ih _ _ _ hv
        exact ⟨by simp [hl],by rw [unframe_spec _ _ _ hu,hs]; simp [frames,List.append_assoc]⟩

/-- Canonical decoding has linear output size even for accepted noncanonical words. -/
def DecodeLengthBound {α : Type} (e : BitEncoding α) (c : ℕ) : Prop :=
  ∀ s a,e.decode s=some a → (e.encode a).length≤c*(s.length+1)

private theorem encode_decodePosNum_length (s : Bits) :
    (Computability.encodePosNum (Computability.decodePosNum s)).length≤s.length+1 := by
  induction s with
  | nil => simp [Computability.encodePosNum,Computability.decodePosNum]
  | cons b bs ih =>
    cases b with
    | false => simp [Computability.encodePosNum,Computability.decodePosNum]; omega
    | true =>
      by_cases h:bs=[]
      · subst bs; simp [Computability.encodePosNum,Computability.decodePosNum]
      · simp [Computability.encodePosNum,Computability.decodePosNum,h]; omega

/-- The pinned natural decoder can expand a raw word by at most one bit. -/
theorem nat_decode_length_bound : DecodeLengthBound nat 1 := by
  intro s n hn
  simp only [nat,Option.some.injEq] at hn
  subst n
  cases s with
  | nil => simp [nat,Computability.decodeNat,Computability.decodeNum,Computability.encodeNat,Computability.encodeNum]
  | cons b bs =>
    simpa [nat,Computability.encodeNat,Computability.decodeNat,Num.of_to_nat,
      Computability.decodeNum,Computability.encodeNum] using encode_decodePosNum_length (b::bs)

theorem unary_decode_length_bound : DecodeLengthBound unaryNat 1 := by
  intro s n hn
  simp only [unaryNat,Option.some.injEq] at hn
  subst n
  simp [unaryNat_length]

/-- Product framing charges the complete first word and the complete suffix. -/
theorem prod_decode_length_bound {α β : Type} {ea : BitEncoding α} {eb : BitEncoding β}
    {ca cb : ℕ} (ha : DecodeLengthBound ea ca) (hb : DecodeLengthBound eb cb) :
    DecodeLengthBound (ea.prod eb) (2*ca+cb+1) := by
  intro s p hp
  cases hu:unframe s with
  | none => simp [prod,hu] at hp
  | some pair =>
    rcases pair with ⟨a,b⟩
    cases hda:ea.decode a with
    | none => simp [prod,hu,hda] at hp
    | some av =>
      cases hdb:eb.decode b with
      | none => simp [prod,hu,hda,hdb] at hp
      | some bv =>
        have he : (av,bv)=p := by simpa [prod,hu,hda,hdb] using hp
        subst p
        have hsa:=ha a av hda
        have hsb:=hb b bv hdb
        have hs:=unframe_spec s a b hu
        have hla : a.length≤s.length := by rw [hs]; simp only [List.length_append,frame_length]; omega
        have hlb : b.length≤s.length := by rw [hs]; simp only [List.length_append,frame_length]; omega
        have hsa' := hsa.trans (Nat.mul_le_mul_left ca (Nat.add_le_add_right hla 1))
        have hsb' := hsb.trans (Nat.mul_le_mul_left cb (Nat.add_le_add_right hlb 1))
        rw [prod_length]
        nlinarith

private theorem map_decode_bound {α : Type} {e : BitEncoding α} {c : ℕ} (he : DecodeLengthBound e c)
    (words : List Bits) (xs : List α) (h : words.mapM e.decode=some xs) :
    xs.length=words.length ∧
      (xs.map (fun x=>(e.encode x).length)).sum≤c*((words.map List.length).sum+words.length) := by
  induction words generalizing xs with
  | nil => simp at h; subst xs; simp
  | cons w words ih =>
    cases hw:e.decode w with
    | none => simp [List.mapM_cons,hw] at h
    | some x =>
      cases ht:words.mapM e.decode with
      | none => simp [List.mapM_cons,hw,ht] at h
      | some ys =>
        have hx : x::ys=xs := by simpa [List.mapM_cons,hw,ht] using h
        subst xs
        obtain ⟨hlen,hsize⟩:=ih ys ht
        have hb:=he w x hw
        constructor
        · simp [hlen]
        · simp only [List.map_cons,List.sum_cons,List.length_cons]
          calc
            _ ≤ c*(w.length+1)+c*((words.map List.length).sum+words.length) := Nat.add_le_add hb hsize
            _ = _ := by ring

/-- Each item delimiter pays for its own fixed canonicalization overhead. -/
theorem list_decode_length_bound {α : Type} {e : BitEncoding α} {c : ℕ}
    (he : DecodeLengthBound e c) : DecodeLengthBound e.list (2*c+3) := by
  intro s xs hs
  cases hu:unframe s with
  | none => simp [list,hu] at hs
  | some p =>
    rcases p with ⟨header,rest⟩
    cases hr:unframes (Computability.decodeNat header) rest with
    | none => simp [list,nat,hu,hr] at hs
    | some p =>
      rcases p with ⟨words,tail⟩
      by_cases ht:tail=[]
      · subst tail
        have hm : words.mapM e.decode=some xs := by simpa [list,nat,hu,hr] using hs
        obtain ⟨hlen,hsize⟩:=map_decode_bound he words xs hm
        obtain ⟨hwords,hrest⟩:=unframes_spec _ _ _ _ hr
        have hsource:=unframe_spec s header rest hu
        have hheader : nat.decode header=some xs.length := by simp [nat,hlen,hwords]
        have hh:=nat_decode_length_bound header xs.length hheader
        have hraw : s.length=2*header.length+1+2*(words.map List.length).sum+words.length := by
          rw [hsource,hrest]
          simp only [List.length_append,frame_length,frames_length,List.append_nil]
          omega
        have hpayload : (words.map List.length).sum+words.length≤s.length := by omega
        have hsz := hsize.trans (Nat.mul_le_mul_left c hpayload)
        have hxlen : xs.length≤s.length := by omega
        have hh' : (nat.encode xs.length).length≤s.length+1 := by simp only [Nat.one_mul] at hh; omega
        simp only [list,List.length_append,frame_length,frames_length,List.length_map,List.map_map,Function.comp_def]
        nlinarith
      · simp [list,nat,hu,hr,ht] at hs

/-- A genuine bijective structural view preserves the same decoder size bound. -/
theorem retract_decode_length_bound {α β : Type} {e : BitEncoding β} {c : ℕ}
    (he : DecodeLengthBound e c) (f : α→β) (g : β→α)
    (hgf : ∀ a,g (f a)=a) (hfg : ∀ b,f (g b)=b) :
    DecodeLengthBound (e.retract f g hgf) c := by
  intro s a h
  cases hd:e.decode s with
  | none => simp [retract,hd] at h
  | some b =>
    have hg : g b=a := by simpa [retract,hd] using h
    subst a
    simpa [retract,hfg] using he s b hd

end BitEncoding

namespace GraphCode

theorem decode_length_bound : BitEncoding.DecodeLengthBound encoding 14 := by
  apply BitEncoding.retract_decode_length_bound
    (BitEncoding.prod_decode_length_bound BitEncoding.unary_decode_length_bound
      (BitEncoding.list_decode_length_bound
        (BitEncoding.prod_decode_length_bound BitEncoding.nat_decode_length_bound
          BitEncoding.nat_decode_length_bound)))
  intro b; cases b; rfl

theorem raw_size_le (bits : Bits) (g : GraphCode) (h : encoding.decode bits=some g) :
    g.vertices+g.edges.length≤14*(bits.length+1) :=
  (g.size_le_length).trans (decode_length_bound bits g h)

end GraphCode

namespace MixedCode

theorem decode_length_bound : BitEncoding.DecodeLengthBound encoding 49 := by
  apply BitEncoding.retract_decode_length_bound
    (BitEncoding.prod_decode_length_bound BitEncoding.unary_decode_length_bound
      (BitEncoding.prod_decode_length_bound
        (BitEncoding.list_decode_length_bound
          (BitEncoding.prod_decode_length_bound BitEncoding.nat_decode_length_bound
            (BitEncoding.prod_decode_length_bound BitEncoding.nat_decode_length_bound
              BitEncoding.nat_decode_length_bound)))
        (BitEncoding.list_decode_length_bound
          (BitEncoding.prod_decode_length_bound BitEncoding.nat_decode_length_bound
            BitEncoding.nat_decode_length_bound))))
  intro b; rcases b with ⟨v,e,u⟩; rfl

theorem raw_size_le (bits : Bits) (g : MixedCode) (h : encoding.decode bits=some g) :
    g.vertices+g.edges.length+g.unaries.length≤49*(bits.length+1) :=
  (g.size_le_length).trans (decode_length_bound bits g h)

end MixedCode
end PlanarHom.Complexity
