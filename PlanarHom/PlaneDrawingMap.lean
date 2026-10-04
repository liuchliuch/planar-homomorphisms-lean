import PlanarHom.PlanarEmbedding

/-! NEW transport of an actual drawing through an injective continuous map. -/
noncomputable section
namespace PlanarHom.HardcoreLogicGadgets
open MultiGraph

def mapPlaneDrawing {V E : Type*} {G : MultiGraph V E} (d : PlaneDrawing G)
    (f : C(Plane,Plane)) (hf : Function.Injective f) : PlaneDrawing G where
  point := fun v=>f (d.point v)
  point_injective := hf.comp d.point_injective
  curve e := f.comp (d.curve e)
  curve_zero e := by simp [d.curve_zero]
  curve_one e := by simp [d.curve_one]
  interior_injective e e' s t hs ht he := d.interior_injective e e' s t hs ht (hf he)
  interior_avoids e t ht v he := d.interior_avoids e t ht v (hf he)

end PlanarHom.HardcoreLogicGadgets
