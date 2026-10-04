import PlanarHom.RepresentedFieldEncoding
import PlanarHom.GraphCodeNormalization

/-! Exact lexical handling of arbitrary valid representative answer lists.
Only the actual presentation normalizer is used at runtime. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity

theorem decode_bits_list {B:Type} (eb:BitEncoding B) (ws:List Bits) :
    eb.list.decode (BitEncoding.bits.list.encode ws)=ws.mapM eb.decode := by
  simp [BitEncoding.list,BitEncoding.bits,BitEncoding.unframe_frame_append,
    BitEncoding.unframes_frames,BitEncoding.nat]

theorem answer_list_codes {A B:Type} (eb:BitEncoding B) (xs:List A) (answers:A→Bits)
    (R:A→B→Prop) (h:∀a∈xs,∃b,eb.decode (answers a)=some b ∧ R a b) :
    ∃bs,eb.list.decode (BitEncoding.bits.list.encode (xs.map answers))=some bs ∧ List.Forall₂ R xs bs := by
  rw [decode_bits_list]
  induction xs with
  | nil=>exact ⟨[],rfl,.nil⟩
  | cons a xs ih=>
    obtain ⟨b,hb,hr⟩:=h a (List.mem_cons_self)
    obtain ⟨bs,hbs,hrs⟩:=ih (fun x hx=>h x (List.mem_cons_of_mem _ hx))
    refine ⟨b::bs,?_,.cons hr hrs⟩
    simp [List.mapM_cons,hb,hbs]

theorem decode_context_answers {A B:Type} (ea:BitEncoding A) (eb:BitEncoding B)
    (a:A) (ws:List Bits) (bs:List B)
    (h:eb.list.decode (BitEncoding.bits.list.encode ws)=some bs) :
    (ea.prod eb.list).decode ((ea.prod BitEncoding.bits.list).encode (a,ws))=some (a,bs) := by
  simp [BitEncoding.prod,ea.decode_encode,h]

end PlanarHom.RepresentedBit
