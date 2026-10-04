import PlanarHom.PrescribedDomainTyping
import PlanarHom.PlanarRibbonExistence

/-! Exact raw-domain promises are invariant under their corresponding positive
parallel queries; the same original δ and permitted label/domain tables remain. -/
namespace PlanarHom.PrescribedDomains
open Complexity Complexity.MixedCode
variable {binaryTypes unaryTypes domainTypes : ℕ}
variable (B : Fin binaryTypes→Fin domainTypes→Fin domainTypes→Prop)
variable (T : Fin unaryTypes→Fin domainTypes→Prop)

def EncodedGraph (g : MixedCode) : Prop:=EncodedInput B T (MixedCode.encoding.encode g)

theorem encodedInput_congr_decode {s t : Bits} (h : MixedCode.encoding.decode s=MixedCode.encoding.decode t) :
    EncodedInput B T s ↔ EncodedInput B T t:=by
  simp only [EncodedInput,h]

theorem encodedInput_iff_graph (raw : Bits) :
    EncodedInput B T raw ↔ ∃g,MixedCode.encoding.decode raw=some g ∧ EncodedGraph B T g:=by
  constructor
  · intro h
    obtain ⟨g,hg,δ,ht,hp,hd⟩:=h
    exact ⟨withDomains (unaryTypes:=unaryTypes) g δ,hd,encodedInput_encode_withDomains ht hp⟩
  · rintro ⟨g,hd,hg⟩
    exact (encodedInput_congr_decode B T (hd.trans (MixedCode.encoding.decode_encode g).symm)).mpr hg

theorem EncodedGraph.planarValid {g : MixedCode} (h : EncodedGraph B T g) :
    g.PlanarValid binaryTypes (unaryTypes+domainTypes):=
  (planarInput_encode_iff _ _ g).mp h.planarInput

theorem EncodedGraph.parallelLabel {g : MixedCode} (h : EncodedGraph B T g) (selected n : ℕ) :
    EncodedGraph B T (g.parallelLabel selected n):=by
  obtain ⟨original,hg,δ,ht,hp,hd⟩:=h
  rw [MixedCode.encoding.decode_encode] at hd
  have he:g=withDomains (unaryTypes:=unaryTypes) original δ:=Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [parallelLabel_withDomains]
  exact encodedInput_encode_withDomains (ht.parallelLabel selected n)
    ((show original.PlanarValid binaryTypes unaryTypes from ⟨hg,hp⟩).parallelLabel selected n).2

theorem EncodedGraph.parallelUnaryLabel {g : MixedCode} (h : EncodedGraph B T g)
    (selected n : ℕ) (hs : selected<unaryTypes) :
    EncodedGraph B T (g.parallelUnaryLabel selected n):=by
  obtain ⟨original,hg,δ,ht,hp,hd⟩:=h
  rw [MixedCode.encoding.decode_encode] at hd
  have he:g=withDomains (unaryTypes:=unaryTypes) original δ:=Option.some.inj hd
  subst g
  unfold EncodedGraph
  rw [parallelUnaryLabel_withDomains original δ selected n hs]
  exact encodedInput_encode_withDomains (ht.parallelUnaryLabel selected n) hp

end PlanarHom.PrescribedDomains
