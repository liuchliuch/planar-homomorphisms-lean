import PlanarHom.CodecDecodingBounds

/-! Raw words whose decoders succeed, retaining every accepted noncanonical word.
The encoding of this subtype is the original word, not its re-encoding. -/
namespace PlanarHom.Complexity.BitEncoding

/-- A representation of successful raw inputs that does not discard alternate
encodings. This is useful for machine witnesses on the full decoding promise. -/
def ValidWord {α : Type} (e : BitEncoding α):= {s : Bits // ∃a,e.decode s=some a}

namespace ValidWord
variable {α : Type} {e : BitEncoding α}
def raw (w : ValidWord e) : Bits:=w.val
noncomputable def value (w : ValidWord e) : α:=Classical.choose w.property
@[simp] theorem decode_raw (w : ValidWord e) : e.decode w.raw=some w.value:=Classical.choose_spec w.property

theorem value_eq {w : ValidWord e} {a : α} (h : e.decode w.raw=some a) : w.value=a:=by
  rw [decode_raw] at h
  exact Option.some.inj h

/-- Decoding this representation validates success only; encoding retains the
original bytes, so valid padded/header alternatives remain distinct inputs. -/
def encoding (e : BitEncoding α) : BitEncoding (ValidWord e) where
  encode:=raw
  decode s:=match h:e.decode s with
    | none=>none
    | some a=>some ⟨s,⟨a,h⟩⟩
  decode_encode w:=by
    dsimp only [raw]
    split
    · rename_i h
      obtain ⟨a,ha⟩:=w.property
      simp_all
    · congr

def canonical (e : BitEncoding α) (a : α) : ValidWord e:=⟨e.encode a,⟨a,e.decode_encode a⟩⟩
@[simp] theorem canonical_value (a : α) : (canonical e a).value=a:=value_eq (e.decode_encode a)

private theorem exists_split {β : Type} (eb : BitEncoding β) (w : ValidWord (e.prod eb)) :
    ∃p : ValidWord e × ValidWord eb,w.raw=frame p.1.raw++p.2.raw:=by
  obtain ⟨p,hp⟩:=w.property
  change (e.prod eb).decode w.raw=some p at hp
  cases hu:unframe w.raw with
  | none=>simp [-decode_raw,prod,hu] at hp
  | some pair=>
    rcases pair with ⟨a,b⟩
    cases hda:e.decode a with
    | none=>simp [-decode_raw,prod,hu,hda] at hp
    | some av=>
      cases hdb:eb.decode b with
      | none=>simp [-decode_raw,prod,hu,hda,hdb] at hp
      | some bv=>
        exact ⟨(⟨a,⟨av,hda⟩⟩,⟨b,⟨bv,hdb⟩⟩),unframe_spec _ _ _ hu⟩

noncomputable def split {β : Type} (eb : BitEncoding β) (w : ValidWord (e.prod eb)) :
    ValidWord e × ValidWord eb:=Classical.choose (exists_split eb w)

theorem split_raw {β : Type} (eb : BitEncoding β) (w : ValidWord (e.prod eb)) :
    w.raw=frame (split eb w).1.raw++(split eb w).2.raw:=Classical.choose_spec (exists_split eb w)

theorem split_value {β : Type} (eb : BitEncoding β) (w : ValidWord (e.prod eb)) :
    w.value=((split eb w).1.value,(split eb w).2.value):=by
  apply value_eq
  rw [split_raw eb w]
  simp [prod,unframe_frame_append,decode_raw]

end ValidWord
end PlanarHom.Complexity.BitEncoding
