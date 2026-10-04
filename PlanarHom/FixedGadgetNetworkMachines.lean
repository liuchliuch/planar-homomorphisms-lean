import PlanarHom.FixedGadgetNetworkCode
import PlanarHom.MixedUnaryParallelMachines
import PlanarHom.ListFlattenMachines
import PlanarHom.ListDecompositionMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryNatConversionMachine

/-! New real finite-control and list-machine compilation for literal attachments.
The fixed family is in finite control; malformed labels select the empty template. -/
noncomputable section
namespace PlanarHom.FixedGadgetNetwork
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives BinaryArithmetic

def gateEncoding : BitEncoding Gate := BitEncoding.nat.prod BitEncoding.nat.list

def networkEncoding : BitEncoding Network :=
  (MixedCode.encoding.prod gateEncoding.list).retract
    (fun n=>(n.base,n.gates)) (fun p=>⟨p.1,p.2⟩) (by intro n; cases n; rfl)

def edgeItemEncoding : BitEncoding (ℕ × ℕ × ℕ) :=
  BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

def unaryItemEncoding : BitEncoding (ℕ × ℕ) := BitEncoding.nat.prod BitEncoding.nat

private theorem fp_getD_fixed (v : ℕ) :
    FP BitEncoding.nat.list BitEncoding.nat (fun ps=>ps.getD v 0) := by
  induction v with
  | zero => exact (ListDecompositionMachines.fp_headD _ 0).congr (fun xs=>by cases xs <;> rfl)
  | succ v ih =>
    exact ((ListDecompositionMachines.fp_tail _ 0).comp ih).congr (fun xs=>by cases xs <;> rfl)

private theorem fp_fixed_map {A X Y : Type} (ex : BitEncoding X) (ey : BitEncoding Y)
    (xs : List A) (f : X→A→Y) (hf : ∀a∈xs,FP ex ey (fun x=>f x a)) :
    FP ex ey.list (fun x=>xs.map (f x)) := by
  induction xs with
  | nil => exact fp_const _ _ []
  | cons a as ih =>
    exact ((hf a (by simp)).pair (ih (fun b hb=>hf b (by simp [hb])))).comp
      (ListMutationMachines.fp_cons ey)

theorem fp_remapVertex (t : Template) (v : ℕ) :
    FP (BitEncoding.unaryNat.prod BitEncoding.nat.list) BitEncoding.nat
      (fun p=>remapVertex t p.1 p.2 v) := by
  by_cases hv : v<t.boundary
  · exact ((fp_snd _ _).comp (fp_getD_fixed v)).congr (fun p=>by simp [remapVertex,hv])
  · have ho := (fp_fst BitEncoding.unaryNat BitEncoding.nat.list).comp
      UnaryNatConversionMachine.fp_conversion
    exact ((ho.pair (fp_const _ _ (v-t.boundary))).comp fp_addition).congr
      (fun p=>by simp [remapVertex,hv])

theorem fp_attachTemplate (t : Template) :
    FP (MixedCode.encoding.prod BitEncoding.nat.list) MixedCode.encoding
      (fun p=>attachTemplate t p.1 p.2) := by
  let input := MixedCode.encoding.prod BitEncoding.nat.list
  have hg := fp_fst MixedCode.encoding BitEncoding.nat.list
  have hp := fp_snd MixedCode.encoding BitEncoding.nat.list
  have hv := hg.comp MixedCode.fp_vertices
  have hctx := hv.pair hp
  have hr (v : ℕ) := hctx.comp (fp_remapVertex t v)
  have he (e : ℕ × ℕ × ℕ) : FP input edgeItemEncoding
      (fun p=>remapEdge t p.1.vertices p.2 e) :=
    (hr e.1).pair ((hr e.2.1).pair (fp_const _ _ e.2.2))
  have hu (u : ℕ × ℕ) : FP input unaryItemEncoding
      (fun p=>remapUnary t p.1.vertices p.2 u) :=
    (hr u.1).pair (fp_const _ _ u.2)
  have hedges := ((hg.comp MixedCode.fp_edges).pair
    (fp_fixed_map input edgeItemEncoding t.edges (fun p e=>remapEdge t p.1.vertices p.2 e)
      (fun e _=>he e))).comp (ListMutationMachines.fp_append edgeItemEncoding)
  have hunaries := ((hg.comp MixedCode.fp_unaries).pair
    (fp_fixed_map input unaryItemEncoding t.unaries (fun p u=>remapUnary t p.1.vertices p.2 u)
      (fun u _=>hu u))).comp (ListMutationMachines.fp_append unaryItemEncoding)
  have hvertices := (hv.pair (fp_const input BitEncoding.unaryNat t.privateCount)).comp
    UnaryPolynomialMachines.fp_add
  exact (hvertices.pair (hedges.pair hunaries)).transportOutput (fun _=>rfl)

theorem compileStep_nil (g : MixedCode) (a : Gate) : compileStep [] g a=g := by
  cases g
  simp [compileStep,gateTemplate,attachTemplate,emptyTemplate]

theorem compileStep_cons (t : Template) (ts : List Template) (g : MixedCode) (a : Gate) :
    compileStep (t::ts) g a =
      if a.1=0 then attachTemplate t g a.2 else compileStep ts g (a.1-1,a.2) := by
  rcases a with ⟨i,ps⟩
  cases i <;> simp [compileStep,gateTemplate]

theorem fp_compileStep (ts : List Template) :
    FP (MixedCode.encoding.prod gateEncoding) MixedCode.encoding
      (fun p=>compileStep ts p.1 p.2) := by
  let input := MixedCode.encoding.prod gateEncoding
  have hg := fp_fst MixedCode.encoding gateEncoding
  have ha := fp_snd MixedCode.encoding gateEncoding
  have hi := ha.comp (fp_fst BitEncoding.nat BitEncoding.nat.list)
  have hp := ha.comp (fp_snd BitEncoding.nat BitEncoding.nat.list)
  induction ts with
  | nil => exact hg.congr (fun p=>(compileStep_nil p.1 p.2).symm)
  | cons t ts ih =>
    have hzero := hi.comp RationalCircuits.fp_nat_isZero
    have hattach := (hg.pair hp).comp (fp_attachTemplate t)
    have hdec := (hi.pair (fp_const input BitEncoding.nat 1)).comp fp_subtraction
    have htail := (hg.pair (hdec.pair hp)).comp ih
    exact (hzero.ite hattach htail).congr (fun p=>(compileStep_cons t ts p.1 p.2).symm)

end PlanarHom.FixedGadgetNetwork
