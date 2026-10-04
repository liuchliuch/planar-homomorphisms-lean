import PlanarHom.PlanarityLRAllPortNoncrossing

/-! NEW direction-independent form of the proved actual LR port noncrossing. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PlanarityLRRawConstraints PlanarityLRConstraints PlanarityLRConstraintBlocks PlanarityRotationCode

theorem nonTree_raw_port_key_noncrossing (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut) (bits : List Bool)
    (hLR : LRCondition g (bitSide bits)) (halign : Aligned (bitSide bits) (alignmentPairs g))
    {e f : ℕ} (he : e < g.edges.length) (hf : f < g.edges.length)
    (het : isTree g e=false) (hft : isTree g f=false) (hne : e≠f)
    (hr : componentRoot g (source g e)=componentRoot g (source g f)) :
    PortNoncrossing (contourKey g bits (e,true)) (contourKey g bits (e,false))
      (contourKey g bits (f,true)) (contourKey g bits (f,false)) := by
  have h := nonTree_port_key_noncrossing g hg bits hLR halign he hf het hft hne hr
  have houtE : outward g e=(e,(outward g e).2) := rfl
  have houtF : outward g f=(f,(outward g f).2) := rfl
  cases hE : (outward g e).2 <;> cases hF : (outward g f).2
  all_goals rw [hE] at houtE; rw [hF] at houtF
  all_goals rw [houtE,houtF] at h
  all_goals simp only [reverse,Bool.not_false,Bool.not_true] at h
  · exact h.swap_left.swap_right
  · exact h.swap_left
  · exact h.swap_right
  · exact h

end PlanarHom.PlanarityLRDirect
