import PlanarHom.CountingCookLevinUniformReferences
import PlanarHom.ListContextMachines
import PlanarHom.UnaryPolynomialMachines
import PlanarHom.UnaryRangeMachines

/-! A single actual polynomial-time machine emits every time layer and every
cell of the Cook-Levin circuit. The clock is unary; register addresses and the
output gate list use the project's binary natural-number encoding. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic Complexity PairProjectionMachines

abbrev gateEncoding := BitEncoding.nat.prod BitEncoding.nat

def fixedOrder (A : Type) [Fintype A] : List A := List.ofFn (Fintype.equivFin A).symm

@[simp] theorem fixedOrder_length (A : Type) [Fintype A] :
    (fixedOrder A).length=Fintype.card A := by simp [fixedOrder]

private theorem fp_fixed_flatMap {A B D : Type} (ea : BitEncoding A) (ed : BitEncoding D)
    (xs : List B) (f : B → A → List D) (hf : ∀ b, FP ea ed.list (f b)) :
    FP ea ed.list (fun a => xs.flatMap (fun b => f b a)) := by
  induction xs with
  | nil => exact fp_const _ _ []
  | cons b xs ih => exact ((hf b).pair ih).comp (ListMutationMachines.fp_append ed)

def setCell (p : RefInput) (i : ℕ) : RefInput := (p.1,(p.2.1,(p.2.2.1,i)))
def setTime (p : RefInput) (t : ℕ) : RefInput := (p.1,(p.2.1,(t,0)))

private theorem fp_setCell : FP (refEncoding.prod BitEncoding.nat) refEncoding
    (fun p : RefInput × ℕ => setCell p.1 p.2) := by
  have hp := fp_fst refEncoding BitEncoding.nat
  have hx := hp.comp (fp_fst _ _)
  have hr := hp.comp (fp_snd _ _)
  have hT := hr.comp (fp_fst _ _)
  have ht := (hr.comp (fp_snd _ _)).comp (fp_fst _ _)
  exact hx.pair (hT.pair (ht.pair (fp_snd _ _)))

private theorem fp_setTime : FP (refEncoding.prod BitEncoding.nat) refEncoding
    (fun p : RefInput × ℕ => setTime p.1 p.2) := by
  have hp := fp_fst refEncoding BitEncoding.nat
  have hx := hp.comp (fp_fst _ _)
  have hT := (hp.comp (fp_snd _ _)).comp (fp_fst _ _)
  exact hx.pair (hT.pair ((fp_snd _ _).pair (fp_const _ _ 0)))

private theorem fp_cellZero : FP refEncoding refEncoding (fun p => setCell p 0) :=
  ((fp_id _).pair (fp_const _ _ 0)).comp fp_setCell

private theorem fp_cellIndex : FP refEncoding BitEncoding.nat (fun p : RefInput => p.2.2.2) :=
  (((fp_snd _ _).comp (fp_snd _ _)).comp (fp_snd _ _))
private theorem fp_timeIndex : FP refEncoding BitEncoding.nat (fun p : RefInput => p.2.2.1) :=
  (((fp_snd _ _).comp (fp_snd _ _)).comp (fp_fst _ _))

private theorem fp_widthUnary : FP refEncoding BitEncoding.unaryNat refWidth := by
  have hx := (fp_fst BitEncoding.bits (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat))).comp
    (show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
      ⟨InputLengthMachine.computer BitEncoding.bits⟩)
  have hT := (fp_snd BitEncoding.bits (BitEncoding.unaryNat.prod (BitEncoding.nat.prod BitEncoding.nat))).comp
    (fp_fst _ _)
  exact (((hx.pair hT).comp UnaryPolynomialMachines.fp_add).pair (fp_const _ _ 1)).comp
    UnaryPolynomialMachines.fp_add

private theorem fp_ascendingRange : FP BitEncoding.unaryNat BitEncoding.nat.list List.range :=
  (UnaryRangeMachines.fp_range.comp (ListReverseMachines.fp_reverse BitEncoding.nat)).congr
    (fun _ => List.reverse_reverse _)

private theorem fp_flatMapRange (f : RefInput → NorGates) (hf : FP refEncoding gateEncoding.list f) :
    FP refEncoding gateEncoding.list (fun p => (List.range (refWidth p)).flatMap (fun i => f (setCell p i))) := by
  have hb := fp_setCell.comp hf
  have hm := ListContextMachines.fp_mapWithContext refEncoding BitEncoding.nat gateEncoding.list _ hb
  exact ((((fp_id _).pair (fp_widthUnary.comp fp_ascendingRange)).comp hm).comp
    (ListFlattenMachines.fp_flatten gateEncoding)).congr (fun _ => by simp [List.flatMap])

def uniformBlockSize (m : Machine) : ℕ := 4*localGateBound m+3

def baseBlock (m : Machine) (C : ℕ) (b : BaseStateBit m) (p : RefInput) : NorGates :=
  let p := setCell p 0
  let f : LocalContext m → Bool := match b with
    | .inl q => fun c => decide (localControl m c=q)
    | .inr (.inl a) => fun c => decide (localHead m c=a)
    | .inr (.inr v) => fun c => decide (localValid m c=v)
  (numericLocalTemplate m f).regularBlock C
    (timeStart m C p+4+4*C*(Fintype.equivFin (BaseStateBit m) b).val) (referenceVector m C false p)

theorem fp_baseBlock (m : Machine) (C : ℕ) (b : BaseStateBit m) :
    FP refEncoding gateEncoding.list (baseBlock m C b) := by
  rcases b with q | (a | v)
  all_goals exact fp_cellZero.comp (fp_uniformLocalBlock m C false _ _ (fp_const _ _ _))

def cellBlock (m : Machine) (C : ℕ) (side : Bool) (a : Option m.Γ) (p : RefInput) : NorGates :=
  (numericLocalTemplate m (fun c => decide (localCell m c=a))).regularBlock C
    (timeStart m C p+4+4*C*cellOrdinal m p side p.2.2.2 a) (referenceVector m C side p)

theorem fp_cellBlock (m : Machine) (C : ℕ) (side : Bool) (a : Option m.Γ) :
    FP refEncoding gateEncoding.list (cellBlock m C side a) :=
  fp_uniformLocalBlock m C side _ _ (fp_cellOrdinal m side a _ fp_cellIndex)

def cellRow (m : Machine) (C : ℕ) (side : Bool) (p : RefInput) : NorGates :=
  (fixedOrder (Option m.Γ)).flatMap (fun a => cellBlock m C side a p)
def sideLayer (m : Machine) (C : ℕ) (side : Bool) (p : RefInput) : NorGates :=
  (List.range (refWidth p)).flatMap (fun i => cellRow m C side (setCell p i))
def baseLayer (m : Machine) (C : ℕ) (p : RefInput) : NorGates :=
  (fixedOrder (BaseStateBit m)).flatMap (fun b => baseBlock m C b p)

def uniformStep (m : Machine) (C : ℕ) (p : RefInput) : NorGates :=
  [(p.2.2.1,p.2.2.1)] ++ baseLayer m C p ++
    (fixedOrder Bool).flatMap (fun side => sideLayer m C side p)

theorem fp_uniformStep (m : Machine) (C : ℕ) : FP refEncoding gateEncoding.list (uniformStep m C) := by
  have hbase := fp_fixed_flatMap refEncoding gateEncoding (fixedOrder (BaseStateBit m))
    (baseBlock m C) (fp_baseBlock m C)
  have hside (s : Bool) : FP refEncoding gateEncoding.list (sideLayer m C s) :=
    fp_flatMapRange _ (fp_fixed_flatMap _ _ (fixedOrder (Option m.Γ)) _ (fp_cellBlock m C s))
  have hsides := fp_fixed_flatMap refEncoding gateEncoding (fixedOrder Bool) (sideLayer m C) hside
  have hpair := fp_timeIndex.pair fp_timeIndex
  have hfirst := (hpair.pair (fp_const refEncoding gateEncoding.list [])).comp (ListMutationMachines.fp_cons gateEncoding)
  exact (((hfirst.pair hbase).comp (ListMutationMachines.fp_append gateEncoding)).pair hsides).comp
    (ListMutationMachines.fp_append gateEncoding)

abbrev ClockedInput := Bits × ℕ
def clockedEncoding : BitEncoding ClockedInput := BitEncoding.bits.prod BitEncoding.unaryNat

def clockContext (p : ClockedInput) : RefInput := (p.1,(p.2,(0,0)))
private theorem fp_clockContext : FP clockedEncoding refEncoding clockContext :=
  (fp_fst _ _).pair ((fp_snd _ _).pair ((fp_const _ _ 0).pair (fp_const _ _ 0)))

def uniformSteps (m : Machine) (C : ℕ) (p : ClockedInput) : NorGates :=
  (List.range p.2).flatMap (fun t => uniformStep m C (setTime (clockContext p) t))

theorem fp_uniformSteps (m : Machine) (C : ℕ) :
    FP clockedEncoding gateEncoding.list (uniformSteps m C) := by
  have hm := ListContextMachines.fp_mapWithContext refEncoding BitEncoding.nat gateEncoding.list _
    (fp_setTime.comp (fp_uniformStep m C))
  have hi := fp_clockContext.pair ((fp_snd BitEncoding.bits BitEncoding.unaryNat).comp fp_ascendingRange)
  exact ((hi.comp hm).comp (ListFlattenMachines.fp_flatten gateEncoding)).congr
    (fun _ => by simp [uniformSteps,List.flatMap])

/-- Time is an explicitly unary input; the output is a materialized list of
binary gate-reference pairs, not an unevaluated circuit family or oracle. -/
theorem fp_clockedCookLevinBody (m : Machine) :
    FP clockedEncoding gateEncoding.list (uniformSteps m (uniformBlockSize m)) := fp_uniformSteps m _

end PlanarHom.CountingCookLevin
