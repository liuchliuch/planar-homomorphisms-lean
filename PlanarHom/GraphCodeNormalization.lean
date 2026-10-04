import PlanarHom.ListHeaderNormalization
import PlanarHom.ListMapMachines

/-! Actual canonicalization of all successfully decoded graph and mixed-graph
words, including noncanonical natural headers, endpoints, and labels. -/
namespace PlanarHom.Complexity.BitEncoding
open Turing PlanarHom.MachineComposition

/-- Header normalization followed by actual map of recursive item normalizers. -/
noncomputable def listNormalizer {α : Type} {e : BitEncoding α} (h : Normalizer e) :
    Normalizer e.list:=by
  let c:=composeComputers (listHeaderComputer e)
    (PlanarHom.ListMapMachines.computer (ValidWord.encoding e) e ValidWord.value h)
  have he : (fun w : ValidWord e.list=>(ValidWord.listParts e w).items.map ValidWord.value)=ValidWord.value:=by
    funext w
    exact (ValidWord.listParts e w).value_eq.symm
  change TM2ComputableInPolyTime (ValidWord.encoding e.list).toFinEncoding e.list.toFinEncoding
    (fun w=>(ValidWord.listParts e w).items.map ValidWord.value) at c
  rw [he] at c
  exact c

end PlanarHom.Complexity.BitEncoding

namespace PlanarHom.Complexity.GraphCode

/-- The input type contains every word accepted by GraphCode.decode, retaining
its original raw bit length. The compiler returns its exact canonical code. -/
noncomputable def normalizer : BitEncoding.Normalizer encoding:=by
  apply BitEncoding.retractNormalizer
    (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat).list)
    (fun g : GraphCode=>(g.vertices,g.edges))
    (fun p=>⟨p.1,p.2⟩)
    (by intro g; cases g; rfl)
    (by intro p; cases p; rfl)
  exact BitEncoding.prodNormalizer BitEncoding.unaryNormalizer
    (BitEncoding.listNormalizer (BitEncoding.prodNormalizer BitEncoding.natNormalizer BitEncoding.natNormalizer))

end PlanarHom.Complexity.GraphCode

namespace PlanarHom.Complexity.MixedCode

/-- All successful raw decodings are normalized; endpoint and label validity
are preserved because the decoded typed MixedCode value itself is unchanged. -/
noncomputable def normalizer : BitEncoding.Normalizer encoding:=by
  apply BitEncoding.retractNormalizer
    (BitEncoding.unaryNat.prod
      (((BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).list).prod
        (BitEncoding.nat.prod BitEncoding.nat).list))
    (fun g : MixedCode=>(g.vertices,g.edges,g.unaries))
    (fun p=>⟨p.1,p.2.1,p.2.2⟩)
    (by intro g; cases g; rfl)
    (by intro p; rcases p with ⟨v,e,u⟩; rfl)
  exact BitEncoding.prodNormalizer BitEncoding.unaryNormalizer
    (BitEncoding.prodNormalizer
      (BitEncoding.listNormalizer (BitEncoding.prodNormalizer BitEncoding.natNormalizer
        (BitEncoding.prodNormalizer BitEncoding.natNormalizer BitEncoding.natNormalizer)))
      (BitEncoding.listNormalizer (BitEncoding.prodNormalizer BitEncoding.natNormalizer BitEncoding.natNormalizer)))

end PlanarHom.Complexity.MixedCode

namespace PlanarHom.Complexity.GraphCode
open Turing

/-- Direct raw-word execution guarantee, usable without knowing the subtype
representation. Every successful decoder input is covered by the same TM2. -/
noncomputable def normalization_outputs (bits : Bits) (g : GraphCode)
    (hd : encoding.decode bits=some g) :
    TM2OutputsInTime normalizer.tm (bits.map normalizer.inputAlphabet.symm)
      (some ((encoding.encode g).map normalizer.outputAlphabet.symm))
      (normalizer.time.eval bits.length):=by
  let w : BitEncoding.ValidWord encoding:=⟨bits,⟨g,hd⟩⟩
  have hv : w.value=g:=BitEncoding.ValidWord.value_eq hd
  have h:=normalizer.outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,w,hv] using h

end PlanarHom.Complexity.GraphCode

namespace PlanarHom.Complexity.MixedCode
open Turing

noncomputable def normalization_outputs (bits : Bits) (g : MixedCode)
    (hd : encoding.decode bits=some g) :
    TM2OutputsInTime normalizer.tm (bits.map normalizer.inputAlphabet.symm)
      (some ((encoding.encode g).map normalizer.outputAlphabet.symm))
      (normalizer.time.eval bits.length):=by
  let w : BitEncoding.ValidWord encoding:=⟨bits,⟨g,hd⟩⟩
  have hv : w.value=g:=BitEncoding.ValidWord.value_eq hd
  have h:=normalizer.outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,w,hv] using h

end PlanarHom.Complexity.MixedCode
