import PlanarHom.ValidEncodedLists
import PlanarHom.StructuralCodeNormalizers

/-! Normalize a raw accepted list's length header while retaining all original
item words, making generic typed list mapping available for recursive decoding. -/
namespace PlanarHom.Complexity.BitEncoding
open Turing PlanarHom.MachineComposition PlanarHom.MachinePairing
open ValidWord

noncomputable def listRawPair {α : Type} (e : BitEncoding α) (w : ValidWord e.list) : Bits × Bits:=
  ((listParts e w).header,frames ((listParts e w).items.map ValidWord.raw))

/-- This is a literal input-codeword view, not a free runtime decoder. -/
theorem listRawPair_encode {α : Type} (e : BitEncoding α) (w : ValidWord e.list) :
    (bits.prod bits).encode (listRawPair e w)=(ValidWord.encoding e.list).encode w:=
  (listParts e w).raw_eq.symm

/-- The natural-header decoder runs on the real raw bits. Accepted item words
are preserved as distinct typed valid-word values until the next map stage. -/
noncomputable def listHeaderComputer {α : Type} (e : BitEncoding α) :
    TM2ComputableInPolyTime (ValidWord.encoding e.list).toFinEncoding
      (ValidWord.encoding e).list.toFinEncoding (fun w=>(listParts e w).items):=by
  let headerMap:=productMapComputers PlanarHom.NatCanonicalizationMachine.decodeComputer
    (idComputableInPolyTime bits.toFinEncoding)
  let c:=transportInputComputer (ValidWord.encoding e.list) (bits.prod bits) (nat.prod bits)
    (listRawPair e) (listRawPair_encode e) headerMap
  apply transportOutputComputer (ValidWord.encoding e.list) (nat.prod bits) (ValidWord.encoding e).list
    (computer:=c)
  intro w
  simp only [Function.comp_apply,Prod.map,listRawPair,prod,list,bits,ValidWord.encoding,id_eq,
    (listParts e w).count_eq]

end PlanarHom.Complexity.BitEncoding
