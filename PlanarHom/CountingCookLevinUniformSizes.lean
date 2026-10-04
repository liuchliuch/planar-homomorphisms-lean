import PlanarHom.CountingCookLevinUniformEmitter

/-! Exact serialized circuit sizes and uniform evaluation of source clocks. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic Complexity PairProjectionMachines

private theorem base_template_bound (m : Machine) (b : BaseStateBit m) :
    (numericLocalTemplate m (match b with
      | .inl q => fun c => decide (localControl m c=q)
      | .inr (.inl a) => fun c => decide (localHead m c=a)
      | .inr (.inr v) => fun c => decide (localValid m c=v))).copyOutput.gates≤uniformBlockSize m := by
  have h := stepLayer_gates_le m (L := 0) (.inl b)
  rcases b with q | (a | v)
  all_goals simp only [stepLayer,wiredTemplate,Expr.gates_rename] at h
  all_goals simp only [Expr.copyOutput_gates,numericLocalTemplate,Expr.gates_rename,uniformBlockSize]
  all_goals omega

private theorem cell_template_bound (m : Machine) (a : Option m.Γ) :
    (numericLocalTemplate m (fun c => decide (localCell m c=a))).copyOutput.gates≤uniformBlockSize m := by
  have h := stepLayer_gates_le m (L := 0) (.inr (false,0,a))
  simp only [stepLayer,wiredTemplate,Expr.gates_rename] at h
  simp only [Expr.copyOutput_gates,numericLocalTemplate,Expr.gates_rename,uniformBlockSize]
  omega

@[simp] theorem baseBlock_length (m : Machine) (b : BaseStateBit m) (p : RefInput) :
    (baseBlock m (uniformBlockSize m) b p).length=uniformBlockSize m :=
  Expr.regularBlock_length _ _ _ _ (base_template_bound m b)

@[simp] theorem cellBlock_length (m : Machine) (side : Bool) (a : Option m.Γ) (p : RefInput) :
    (cellBlock m (uniformBlockSize m) side a p).length=uniformBlockSize m :=
  Expr.regularBlock_length _ _ _ _ (cell_template_bound m a)

private theorem length_flatMap_const {A B : Type} (xs : List A) (f : A → List B) (n : ℕ)
    (h : ∀ a,(f a).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [ih,h,Nat.add_mul,Nat.add_comm]

@[simp] theorem cellRow_length (m : Machine) (side : Bool) (p : RefInput) :
    (cellRow m (uniformBlockSize m) side p).length=Fintype.card (Option m.Γ)*uniformBlockSize m := by
  rw [cellRow,length_flatMap_const _ _ _ (fun a => cellBlock_length m side a p),fixedOrder_length]

@[simp] theorem sideLayer_length (m : Machine) (side : Bool) (p : RefInput) :
    (sideLayer m (uniformBlockSize m) side p).length=
      refWidth p*(Fintype.card (Option m.Γ)*uniformBlockSize m) := by
  rw [sideLayer,length_flatMap_const _ _ _ (fun i => cellRow_length m side (setCell p i)),List.length_range]

@[simp] theorem baseLayer_length (m : Machine) (p : RefInput) :
    (baseLayer m (uniformBlockSize m) p).length=Fintype.card (BaseStateBit m)*uniformBlockSize m := by
  rw [baseLayer,length_flatMap_const _ _ _ (fun b => baseBlock_length m b p),fixedOrder_length]

@[simp] theorem uniformStep_length (m : Machine) (p : RefInput) :
    (uniformStep m (uniformBlockSize m) p).length=1+uniformBlockSize m*refStateCount m p := by
  simp only [uniformStep,List.length_append,List.length_singleton,baseLayer_length]
  rw [length_flatMap_const _ _ _ (fun s => sideLayer_length m s p),fixedOrder_length,Fintype.card_bool]
  simp only [refStateCount]
  ring

@[simp] theorem uniformSteps_length (m : Machine) (p : ClockedInput) :
    (uniformSteps m (uniformBlockSize m) p).length=
      p.2*(1+uniformBlockSize m*stateRegisterCount m (p.1.length+p.2)) := by
  have h (t : ℕ) : (uniformStep m (uniformBlockSize m) (setTime (clockContext p) t)).length=
      1+uniformBlockSize m*stateRegisterCount m (p.1.length+p.2) :=
    uniformStep_length m (setTime (clockContext p) t)
  rw [uniformSteps,length_flatMap_const _ _ _ h,List.length_range]

def acceptingReference (m : Machine) (C : ℕ) (p : RefInput) : ℕ :=
  stateReference m C p (Fintype.equivFin (BaseStateBit m) (.inl .accept)).val false

def validReference (m : Machine) (C : ℕ) (p : RefInput) : ℕ :=
  stateReference m C p (Fintype.equivFin (BaseStateBit m) (.inr (.inr true))).val true

/-- Three gates implement accepting-control AND validity. -/
def finalGates (m : Machine) (C : ℕ) (p : RefInput) : NorGates :=
  [(acceptingReference m C p,acceptingReference m C p),
   (validReference m C p,validReference m C p),(timeStart m C p,timeStart m C p+4)]

theorem fp_finalGates (m : Machine) (C : ℕ) : FP refEncoding gateEncoding.list (finalGates m C) := by
  have ha : FP refEncoding BitEncoding.nat (acceptingReference m C) :=
    fp_stateReference m C _ _ (fp_const _ _ _) (fp_const _ _ false)
  have hv : FP refEncoding BitEncoding.nat (validReference m C) :=
    fp_stateReference m C _ _ (fp_const _ _ _) (fp_const _ _ true)
  have ht := fp_timeStart m C
  have ht' := (ht.pair (fp_const refEncoding BitEncoding.nat 4)).comp BinaryArithmetic.fp_addition
  have h3 := ((ht.pair ht').pair (fp_const refEncoding gateEncoding.list [])).comp
    (ListMutationMachines.fp_cons gateEncoding)
  have h2 := ((hv.pair hv).pair h3).comp (ListMutationMachines.fp_cons gateEncoding)
  exact ((ha.pair ha).pair h2).comp (ListMutationMachines.fp_cons gateEncoding)

def finalContext (p : ClockedInput) : RefInput := (p.1,(p.2,(p.2,0)))

private theorem fp_finalContext : FP clockedEncoding refEncoding finalContext := by
  have hx := fp_fst BitEncoding.bits BitEncoding.unaryNat
  have hT := fp_snd BitEncoding.bits BitEncoding.unaryNat
  exact hx.pair (hT.pair ((hT.comp UnaryNatConversionMachine.fp_conversion).pair (fp_const _ _ 0)))

def uniformProgram (m : Machine) (p : ClockedInput) : NorGates :=
  uniformSteps m (uniformBlockSize m) p ++ finalGates m (uniformBlockSize m) (finalContext p)

theorem fp_uniformProgram (m : Machine) : FP clockedEncoding gateEncoding.list (uniformProgram m) :=
  ((fp_uniformSteps m _).pair (fp_finalContext.comp (fp_finalGates m _))).comp
    (ListMutationMachines.fp_append gateEncoding)

@[simp] theorem uniformProgram_length (m : Machine) (p : ClockedInput) :
    (uniformProgram m p).length=
      p.2*(1+uniformBlockSize m*stateRegisterCount m (p.1.length+p.2))+3 := by
  simp [uniformProgram,finalGates]

/-- The source time polynomial is physically evaluated in unary, so no binary
clock is silently interpreted as a free exponentially long loop. -/
theorem fp_polynomialClock (p : Polynomial ℕ) :
    FP BitEncoding.bits clockedEncoding (fun x : Bits => (x,p.eval x.length)) :=
  (fp_id _).pair ((show FP BitEncoding.bits BitEncoding.unaryNat (fun x : Bits => x.length) from
    ⟨InputLengthMachine.computer BitEncoding.bits⟩).comp (UnaryPolynomialMachines.fp_eval p))

def sourceProgram (M : PolynomialMachine) (x : Bits) : NorGates :=
  uniformProgram M.machine (x,M.time.eval x.length)

/-- Unconditional actual compiler from the independent single-tape #P source
input to its materialized binary-address NOR gate list. Semantic replay of this
serialized list is proved separately; no circuit-hardness premise occurs here. -/
theorem fp_sourceProgram (M : PolynomialMachine) : FP BitEncoding.bits gateEncoding.list (sourceProgram M) :=
  (fp_polynomialClock M.time).comp (fp_uniformProgram M.machine)

end PlanarHom.CountingCookLevin
