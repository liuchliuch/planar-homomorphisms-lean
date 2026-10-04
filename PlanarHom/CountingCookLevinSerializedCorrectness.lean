import PlanarHom.CountingCookLevinStoreSimulation
import PlanarHom.CountingCookLevinCircuitFamily

/-! Full counting-correctness of the actual polynomial-time serialized compiler. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

def prefixProgram (m : Machine) (x : Complexity.Bits) (T t : ℕ) : NorGates :=
  (List.range t).flatMap (fun j => uniformStep m (uniformBlockSize m) (x,(T,(j,0))))

theorem prefixProgram_succ (m : Machine) (x : Complexity.Bits) (T t : ℕ) :
    prefixProgram m x T (t+1)=prefixProgram m x T t ++ uniformStep m (uniformBlockSize m) (x,(T,(t,0))) := by
  simp [prefixProgram,List.range_succ]

/-- Induction on actual emitted layer prefixes consumes exactly one original
witness bit at each step; it never guesses auxiliary Boolean values. -/
theorem prefixProgram_represents (m : Machine) (x : Complexity.Bits) (T : ℕ) (w : Fin T → Bool)
    (t : ℕ) (ht : t≤T) :
    StoreRepresents m (x,(T,(t,0))) (runNor (prefixProgram m x T t) (initialStore w))
      (((List.ofFn w).take t).foldl (windowStep m) (encodeWindow m (x.length+T) (initial m x),true)) := by
  induction t with
  | zero => simpa [prefixProgram] using initialStore_represents m x T w
  | succ t ih =>
    have h := ih (by omega)
    have hstep := h.step m (x,(T,(t,0))) _ _
    have hread : readBit (runNor (prefixProgram m x T t) (initialStore w)) t=w ⟨t,by omega⟩ := by
      rw [runNor_read_old _ _ _ (by simp; omega)]
      exact initialStore_read w ⟨t,by omega⟩
    rw [hread] at hstep
    rw [prefixProgram_succ,runNor_append]
    have htake : (List.ofFn w).take (t+1)=(List.ofFn w).take t ++ [w ⟨t,by omega⟩] := by
      have hti : t<(List.ofFn w).length := by simp; omega
      calc
        _ = (List.ofFn w).take t ++ [(List.ofFn w)[t]] := (List.take_concat_get' (List.ofFn w) t hti).symm
        _ = _ := by rw [List.getElem_ofFn]
    rw [htake,List.foldl_append,List.foldl_cons,List.foldl_nil]
    exact hstep

theorem uniformSteps_represents (m : Machine) (x : Complexity.Bits) (T : ℕ) (w : Fin T → Bool) :
    StoreRepresents m (finalContext (x,T)) (runNor (uniformSteps m (uniformBlockSize m) (x,T)) (initialStore w))
      ((List.ofFn w).foldl (windowStep m) (encodeWindow m (x.length+T) (initial m x),true)) := by
  simpa only [List.take_of_length_le (show (List.ofFn w).length≤T by simp)] using
    prefixProgram_represents m x T w T (le_refl T)

/-- The three final gates read the actual accepting and validity registers. -/
theorem finalGates_correct (m : Machine) (p : RefInput) (xs : List Bool)
    (s : ReplayState m (p.1.length+p.2.1)) (h : StoreRepresents m p xs s) :
    readBit (runNor (finalGates m (uniformBlockSize m) p) xs)
      (timeStart m (uniformBlockSize m) p+8)=finalBit m s := by
  let e : Expr (Fin 2) := Expr.conj (.var 0) (.var 1)
  let ρ : Fin 2 → ℕ := ![acceptingReference m (uniformBlockSize m) p,validReference m (uniformBlockSize m) p]
  have hb (i : Fin 2) : ρ i<xs.length := by
    fin_cases i <;> dsimp [ρ] <;> rw [h.length_eq]
    all_goals apply stateReference_lt m _ (uniformBlockSize_pos m) p
    all_goals exact (Fintype.equivFin (BaseStateBit m) _).isLt.trans_le (by unfold refStateCount; omega)
  have hc := e.emit_correct ρ xs hb
  have ha : readBit xs (acceptingReference m (uniformBlockSize m) p)=stateBits m s (StateBit.control m .accept) := by
    simpa [acceptingReference,StateBit.control,initialBit] using h.state (StateBit.control m .accept)
  have hv : readBit xs (validReference m (uniformBlockSize m) p)=stateBits m s (StateBit.valid m true) := by
    simpa [validReference,StateBit.valid,initialBit] using h.state (StateBit.valid m true)
  have hem : e.emit xs.length ρ=finalGates m (uniformBlockSize m) p := by
    simp [e,Expr.conj,Expr.neg,Expr.emit,Expr.output,Expr.gates,ρ,finalGates,h.length_eq]
  have hout : e.output xs.length ρ=timeStart m (uniformBlockSize m) p+8 := by
    simp [e,Expr.conj,Expr.neg,Expr.output,Expr.gates,h.length_eq]
  rw [hem,hout] at hc
  simp only [e,Expr.eval_conj,Expr.eval,ρ,Matrix.cons_val_zero,Matrix.cons_val_one] at hc
  rw [ha,hv] at hc
  exact hc.trans (circuitAccept_correct m s)

/-- Actual serialized program value. Only the T source witness bits are free. -/
def serializedValue (m : Machine) (x : Complexity.Bits) (T : ℕ) (w : Fin T → Bool) : Bool :=
  readBit (runNor (uniformProgram m (x,T)) (initialStore w))
    (timeStart m (uniformBlockSize m) (finalContext (x,T))+8)

theorem serializedValue_eq_finiteReplay (m : Machine) (x : Complexity.Bits) (T : ℕ) (w : Fin T → Bool) :
    serializedValue m x T w=finiteReplay m x T w := by
  rw [serializedValue,uniformProgram,runNor_append]
  rw [finalGates_correct m _ _ _ (uniformSteps_represents m x T w),finiteReplay_eq_fold]

/-- Exact counting preservation for the real compiled flat NOR gate list. -/
theorem count_eq_serializedValue (M : PolynomialMachine) (x : Complexity.Bits) :
    M.count x=Fintype.card {w : Fin (M.time.eval x.length) → Bool //
      serializedValue M.machine x (M.time.eval x.length) w=true} := by
  simp_rw [serializedValue_eq_finiteReplay]
  exact count_eq_finiteReplay M x

end PlanarHom.CountingCookLevin
