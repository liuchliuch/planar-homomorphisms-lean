import PlanarHom.SurfaceRawQuotientCoordinates
import PlanarHom.SurfaceCharacterSemantics

/-! NEW exact readout of the executable quotient encoding and chain lift on
finite occurrence vectors. -/
noncomputable section
namespace PlanarHom.SurfaceRawHomology
open SurfaceBooleanRows Complexity PlanarityLRRealization
variable (g : MixedCode) {bt ut : ℕ} (hg : g.Valid bt ut)
variable (rows : PlanarityRowFaceCode.Rows) (R : RotationRows (g.toMultiGraph hg))
variable (hrows : PlanarityRowFaceCode.Realizes g hg rows R)

theorem encode_value (r : Row) (hr : r.length≤g.edges.length) :
    finiteValue (dimension g rows) (encodeQuotient (data g rows) r)=
      (computedCoordinates g hg rows R hrows).encode (finiteValue g.edges.length r) := by
  funext i
  have he := encodeQuotient_value (faceRows g rows) (cycleRows g) r i
  change value (encodeQuotient (data g rows) r) i.val=_
  dsimp only [data]
  rw [he]
  have hval : value r=extendVector g.edges.length (finiteValue g.edges.length r) :=
    (extend_restrict _ _ (value_bounded _ _ hr)).symm
  rw [hval]
  rfl

theorem lift_value (bits : Row) :
    finiteValue g.edges.length (liftQuotient (data g rows) bits)=
      ((computedCoordinates g hg rows R hrows).lift (finiteValue (dimension g rows) bits)).val := by
  funext e
  exact congrFun (liftQuotient_value (faceRows g rows) (cycleRows g) bits) e.val

theorem encode_length (r : Row) : (encodeQuotient (data g rows) r).length=dimension g rows := by
  simp [encodeQuotient,coefficients_eq,dimension]

theorem unit_finiteValue (e : Fin g.edges.length) :
    finiteValue g.edges.length (unit (shape g) e.val)=Pi.single e (1:ZMod 2) := by
  funext f
  simp [finiteValue,value,unit,shape,bitAt,bitValue,Pi.single_apply,Fin.ext_iff,f.isLt,eq_comm]

theorem encode_unit (e : Fin g.edges.length) :
    finiteValue (dimension g rows) (encodeQuotient (data g rows) (unit (shape g) e.val))=
      (computedCoordinates g hg rows R hrows).encode (Pi.single e 1) := by
  rw [encode_value g hg rows R hrows _ (by simp),unit_finiteValue]

end PlanarHom.SurfaceRawHomology
