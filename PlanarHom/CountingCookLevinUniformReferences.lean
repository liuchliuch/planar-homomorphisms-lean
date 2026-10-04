import PlanarHom.CountingCookLevinInitialMachines
import PlanarHom.CountingCookLevinIndexExpressions
import PlanarHom.CountingCookLevinRegularBlocks

/-! Actual polynomial-time source-input, clock, and register-address computation
for the Cook-Levin local block emitter. The clock is physically unary. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic Complexity PairProjectionMachines ArithmeticCircuitPrimitives

/-- Original input, unary clock, time index, and tape-cell index. -/
abbrev RefInput := Bits × (ℕ × (ℕ × ℕ))
def refEncoding : BitEncoding RefInput :=
  BitEncoding.bits.prod (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat))

def refWidth (p : RefInput) : ℕ := p.1.length+p.2.1+1

def refStateCount (m : Machine) (p : RefInput) : ℕ :=
  Fintype.card (BaseStateBit m)+2*(refWidth p*Fintype.card (Option m.Γ))

def timeStart (m : Machine) (C : ℕ) (p : RefInput) : ℕ :=
  p.2.1+4+4*(1+C*refStateCount m p)*p.2.2.1

def groundReference (p : RefInput) (b : Bool) : ℕ := p.2.1+(if b then 0 else 1)

def stateReference (m : Machine) (C : ℕ) (p : RefInput) (slot : ℕ) (initialBit : Bool) : ℕ :=
  if p.2.2.1=0 then groundReference p initialBit else
    p.2.1+4+4*(1+C*refStateCount m p)*(p.2.2.1-1)+4+4*C*slot+4*(C-1)

def cellOrdinal (m : Machine) (p : RefInput) (side : Bool) (i : ℕ) (a : Option m.Γ) : ℕ :=
  Fintype.card (BaseStateBit m)+(refWidth p*Fintype.card (Option m.Γ))*(Fintype.equivFin Bool side).val+
    Fintype.card (Option m.Γ)*i+(Fintype.equivFin (Option m.Γ) a).val

def cellReference (m : Machine) (C : ℕ) (side : Bool) (a : Option m.Γ) (p : RefInput) (i : ℕ) : ℕ :=
  stateReference m C p (cellOrdinal m p side i a) (initialCellTest m a (p.1,(side,i)))

private theorem fp_x : FP refEncoding BitEncoding.bits (fun p : RefInput => p.1) := fp_fst _ _
private theorem fp_tail : FP refEncoding (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat))
    (fun p : RefInput => p.2) := fp_snd _ _
private theorem fp_clock : FP refEncoding BitEncoding.nat (fun p : RefInput => p.2.1) :=
  (fp_tail.comp (fp_fst _ _)).comp UnaryNatConversionMachine.fp_conversion
private theorem fp_indices : FP refEncoding (BitEncoding.nat.prod BitEncoding.nat)
    (fun p : RefInput => p.2.2) := fp_tail.comp (fp_snd _ _)
private theorem fp_time : FP refEncoding BitEncoding.nat (fun p : RefInput => p.2.2.1) :=
  fp_indices.comp (fp_fst _ _)
private theorem fp_cell : FP refEncoding BitEncoding.nat (fun p : RefInput => p.2.2.2) :=
  fp_indices.comp (fp_snd _ _)

private theorem nat_add {A : Type} {e : BitEncoding A} {f g : A → ℕ}
    (hf : FP e BitEncoding.nat f) (hg : FP e BitEncoding.nat g) : FP e BitEncoding.nat (fun a => f a+g a) :=
  (hf.pair hg).comp BinaryArithmetic.fp_addition
private theorem nat_mul {A : Type} {e : BitEncoding A} {f g : A → ℕ}
    (hf : FP e BitEncoding.nat f) (hg : FP e BitEncoding.nat g) : FP e BitEncoding.nat (fun a => f a*g a) :=
  (hf.pair hg).comp BinaryArithmetic.fp_multiplication
private theorem nat_sub {A : Type} {e : BitEncoding A} {f g : A → ℕ}
    (hf : FP e BitEncoding.nat f) (hg : FP e BitEncoding.nat g) : FP e BitEncoding.nat (fun a => f a-g a) :=
  (hf.pair hg).comp BinaryArithmetic.fp_subtraction

private theorem fp_width : FP refEncoding BitEncoding.nat refWidth := by
  have hn := (fp_x.comp (show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
    ⟨InputLengthMachine.computer BitEncoding.bits⟩)).comp UnaryNatConversionMachine.fp_conversion
  exact nat_add (nat_add hn fp_clock) (fp_const _ _ 1)

private theorem fp_stateCount (m : Machine) : FP refEncoding BitEncoding.nat (refStateCount m) :=
  nat_add (fp_const _ _ (Fintype.card (BaseStateBit m)))
    (nat_mul (fp_const _ _ 2) (nat_mul fp_width (fp_const _ _ (Fintype.card (Option m.Γ)))))

private theorem fp_stride (m : Machine) (C : ℕ) :
    FP refEncoding BitEncoding.nat (fun p => 4*(1+C*refStateCount m p)) :=
  nat_mul (fp_const _ _ 4) (nat_add (fp_const _ _ 1) (nat_mul (fp_const _ _ C) (fp_stateCount m)))

theorem fp_timeStart (m : Machine) (C : ℕ) : FP refEncoding BitEncoding.nat (timeStart m C) :=
  nat_add (nat_add fp_clock (fp_const _ _ 4)) (nat_mul (fp_stride m C) fp_time)

theorem fp_groundReference (b : RefInput → Bool) (hb : FP refEncoding BitEncoding.bool b) :
    FP refEncoding BitEncoding.nat (fun p => groundReference p (b p)) :=
  nat_add fp_clock (hb.comp (fp_bool_unary BitEncoding.nat (fun b => if b then 0 else 1)))

theorem fp_stateReference (m : Machine) (C : ℕ) (slot : RefInput → ℕ) (initialBit : RefInput → Bool)
    (hs : FP refEncoding BitEncoding.nat slot) (hb : FP refEncoding BitEncoding.bool initialBit) :
    FP refEncoding BitEncoding.nat (fun p => stateReference m C p (slot p) (initialBit p)) := by
  have hzero := fp_time.comp RationalCircuits.fp_nat_isZero
  have hp := nat_add (nat_add (nat_add
    (nat_add fp_clock (fp_const _ _ 4))
      (nat_mul (fp_stride m C) (nat_sub fp_time (fp_const _ _ 1)))) (fp_const _ _ 4))
        (nat_mul (fp_const _ _ (4*C)) hs)
  have hprior := nat_add hp (fp_const _ _ (4*(C-1)))
  exact hzero.ite (fp_groundReference initialBit hb) hprior

theorem fp_cellOrdinal (m : Machine) (side : Bool) (a : Option m.Γ)
    (i : RefInput → ℕ) (hi : FP refEncoding BitEncoding.nat i) :
    FP refEncoding BitEncoding.nat (fun p => cellOrdinal m p side (i p) a) :=
  nat_add (nat_add (nat_add (fp_const _ _ (Fintype.card (BaseStateBit m)))
    (nat_mul (nat_mul fp_width (fp_const _ _ (Fintype.card (Option m.Γ))))
      (fp_const _ _ (Fintype.equivFin Bool side).val)))
    (nat_mul (fp_const _ _ (Fintype.card (Option m.Γ))) hi))
      (fp_const _ _ (Fintype.equivFin (Option m.Γ) a).val)

theorem fp_cellReference (m : Machine) (C : ℕ) (side : Bool) (a : Option m.Γ)
    (i : RefInput → ℕ) (hi : FP refEncoding BitEncoding.nat i) :
    FP refEncoding BitEncoding.nat (fun p => cellReference m C side a p (i p)) :=
  fp_stateReference m C _ _ (fp_cellOrdinal m side a i hi)
    ((fp_x.pair ((fp_const refEncoding BitEncoding.bool side).pair hi)).comp (fp_initialCellTest m a))

/-- Literal uniform reference calculation for one fixed local template input. -/
def localReference (m : Machine) (C : ℕ) (side : Bool) (p : RefInput) : LocalBit m ⊕ Bool → ℕ
  | .inr b => groundReference p b
  | .inl (.control q) => stateReference m C p
      (Fintype.equivFin (BaseStateBit m) (.inl q)).val (decide (Control.run m.start=q))
  | .inl (.head a) => stateReference m C p
      (Fintype.equivFin (BaseStateBit m) (.inr (.inl a))).val (initialHeadTest m a p.1)
  | .inl (.valid b) => stateReference m C p
      (Fintype.equivFin (BaseStateBit m) (.inr (.inr b))).val (decide (true=b))
  | .inl (.choice b) => if b then p.2.2.1 else timeStart m C p
  | .inl (.leftHead a) => cellReference m C true a p 0
  | .inl (.rightHead a) => cellReference m C false a p 0
  | .inl (.current a) => cellReference m C side a p p.2.2.2
  | .inl (.previous a) => if p.2.2.2=0 then groundReference p (decide (none=a))
      else cellReference m C side a p (p.2.2.2-1)
  | .inl (.next a) => if p.2.2.2+1<refWidth p then cellReference m C side a p (p.2.2.2+1)
      else groundReference p (decide (none=a))
  | .inl (.first b) => groundReference p (decide ((decide (p.2.2.2=0))=b))
  | .inl (.leftSide b) => groundReference p (decide (side=b))

theorem fp_localReference (m : Machine) (C : ℕ) (side : Bool) (v : LocalBit m ⊕ Bool) :
    FP refEncoding BitEncoding.nat (fun p => localReference m C side p v) := by
  cases v with
  | inr b => exact fp_groundReference _ (fp_const _ _ b)
  | inl v =>
    cases v with
    | control q => exact fp_stateReference m C _ _ (fp_const _ _ _) (fp_const _ _ _)
    | head a => exact fp_stateReference m C _ _ (fp_const _ _ _) (fp_x.comp (fp_initialHeadTest m a))
    | valid b => exact fp_stateReference m C _ _ (fp_const _ _ _) (fp_const _ _ _)
    | choice b => cases b; exact fp_timeStart m C; exact fp_time
    | leftHead a => exact fp_cellReference m C true a _ (fp_const _ _ 0)
    | rightHead a => exact fp_cellReference m C false a _ (fp_const _ _ 0)
    | current a => exact fp_cellReference m C side a _ fp_cell
    | previous a =>
      exact (fp_cell.comp RationalCircuits.fp_nat_isZero).ite
        (fp_groundReference _ (fp_const _ _ _))
        (fp_cellReference m C side a _ (nat_sub fp_cell (fp_const _ _ 1)))
    | next a =>
      have hn := nat_add fp_cell (fp_const _ _ 1)
      exact ((hn.pair fp_width).comp BinaryArithmetic.fp_comparison).ite
        (fp_cellReference m C side a _ hn) (fp_groundReference _ (fp_const _ _ _))
    | first b =>
      exact fp_groundReference _
        ((fp_cell.comp RationalCircuits.fp_nat_isZero).comp (fp_bool_unary BitEncoding.bool (fun z => decide (z=b))))
    | leftSide b => exact fp_groundReference _ (fp_const _ _ _)

def referenceVector (m : Machine) (C : ℕ) (side : Bool) (p : RefInput) :
    Fin (Fintype.card (LocalBit m ⊕ Bool)) → ℕ :=
  fun i => localReference m C side p ((Fintype.equivFin (LocalBit m ⊕ Bool)).symm i)

theorem fp_referenceVector (m : Machine) (C : ℕ) (side : Bool) :
    FP refEncoding (BitEncoding.nat.vector (Fintype.card (LocalBit m ⊕ Bool))) (referenceVector m C side) :=
  FixedVectorMachines.fp_assemble _ _ _ _ (fun i => fp_localReference m C side _)

/-- A uniform actual machine emits one complete width/clock-dependent block;
only the output tag/transition template are fixed finite program data. -/
theorem fp_uniformLocalBlock (m : Machine) (C : ℕ) (side : Bool)
    (f : LocalContext m → Bool) (slot : RefInput → ℕ) (hs : FP refEncoding BitEncoding.nat slot) :
    FP refEncoding (BitEncoding.nat.prod BitEncoding.nat).list
      (fun p => (numericLocalTemplate m f).regularBlock C (timeStart m C p+4+4*C*slot p)
        (referenceVector m C side p)) := by
  have hstart := nat_add (nat_add (fp_timeStart m C) (fp_const _ _ 4)) (nat_mul (fp_const _ _ (4*C)) hs)
  exact (hstart.pair (fp_referenceVector m C side)).comp (Expr.fp_regularBlock (numericLocalTemplate m f) C)

end PlanarHom.CountingCookLevin
