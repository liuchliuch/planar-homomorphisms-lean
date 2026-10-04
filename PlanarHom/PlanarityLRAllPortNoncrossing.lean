import PlanarHom.PlanarityLRBackPortNoncrossing
import PlanarHom.PlanarityLRLoopPortNoncrossing

/-! NEW complete computed non-tree port noninterleaving, including every literal
loop and parallel occurrence. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityLRRawConstraints PlanarityLRConstraints PlanarityRotationCode PlanarityLRConstraintBlocks

 theorem nonTree_loop_or_back (g : MixedCode) {e : ℕ} (he : e < g.edges.length) (ht : isTree g e=false) :
    (edge g e).1=(edge g e).2.1 ∨ isBack g e=true := by
  by_cases h : (edge g e).1=(edge g e).2.1
  · exact Or.inl h
  · right
    have hst := (source_ne_target_iff g e).mpr h
    simp [isBack,he,ht,hst]

 theorem nonTree_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (bits : List Bool) (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {e f : ℕ} (he : e < g.edges.length) (hf : f < g.edges.length) (het : isTree g e=false) (hft : isTree g f=false)
    (hne : e≠f) (hr : componentRoot g (source g e)=componentRoot g (source g f)) :
    PortNoncrossing (contourKey g bits (outward g e)) (contourKey g bits (reverse (outward g e)))
      (contourKey g bits (outward g f)) (contourKey g bits (reverse (outward g f))) := by
  rcases nonTree_loop_or_back g he het with hel | heb
  · exact PlanarityLRRealization.loop_port_key_noncrossing g hg bits he hf hel hne hr
  · rcases nonTree_loop_or_back g hf hft with hfl | hfb
    · exact (PlanarityLRRealization.loop_port_key_noncrossing g hg bits hf he hfl hne.symm hr.symm).symm
    · exact back_port_key_noncrossing g hg bits hLR halign heb hfb hne hr

 theorem computed_nonTree_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
    (hflag : (decideAligned g).1=true) {e f : ℕ} (he : e < g.edges.length) (hf : f < g.edges.length)
    (het : isTree g e=false) (hft : isTree g f=false) (hne : e≠f)
    (hr : componentRoot g (source g e)=componentRoot g (source g f)) :
    PortNoncrossing (contourKey g (decideAligned g).2 (outward g e))
      (contourKey g (decideAligned g).2 (reverse (outward g e)))
      (contourKey g (decideAligned g).2 (outward g f))
      (contourKey g (decideAligned g).2 (reverse (outward g f))) := by
  have h := decideAligned_sound g hflag
  exact nonTree_port_key_noncrossing g hg (decideAligned g).2 h.1 h.2 he hf het hft hne hr

end PlanarHom.PlanarityLRDirect
