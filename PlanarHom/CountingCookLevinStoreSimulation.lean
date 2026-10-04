import PlanarHom.CountingCookLevinRegisterBounds

/-! Simulation invariant for the actually emitted flat NOR program. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

structure StoreRepresents (m : Machine) (p : RefInput) (xs : List Bool)
    (s : ReplayState m (p.1.length+p.2.1)) : Prop where
  length_eq : xs.length=timeStart m (uniformBlockSize m) p
  ground : ∀ b,readBit xs (groundReference p b)=b
  state : ∀ out,readBit xs
    (stateReference m (uniformBlockSize m) p (stateOrdinal m out) (initialBit m p.1 out))=stateBits m s out

def nextContext (p : RefInput) : RefInput := setTime p (p.2.2.1+1)

/-- One emitted time layer simulates the source step with the literal witness
bit at its original register. Grounds and previous registers remain shared. -/
theorem StoreRepresents.step (m : Machine) (p : RefInput) (xs : List Bool)
    (s : ReplayState m (p.1.length+p.2.1)) (h : StoreRepresents m p xs s) :
    StoreRepresents m (nextContext p) (runNor (uniformStep m (uniformBlockSize m) p) xs)
      (windowStep m s (readBit xs p.2.2.1)) := by
  let C := uniformBlockSize m
  let ys := norStep xs (p.2.2.1,p.2.2.1)
  have hlen : ys.length=timeStart m C p+4 := by simp [ys,h.length_eq,C]
  have hread (v : LayerInput m (p.1.length+p.2.1)) :
      readBit ys (globalReference m C p v)=layerInputs m s (readBit xs p.2.2.1) v := by
    rcases v with (out | b) | b
    · change readBit ys (stateReference m C p (stateOrdinal m out) (initialBit m p.1 out))=_
      rw [norStep_read_old xs _ _ (by
        rw [h.length_eq]
        exact stateReference_lt m C (uniformBlockSize_pos m) p _ _ (stateIndexEquiv m _ out).isLt)]
      exact h.state out
    · cases b
      · change readBit ys (timeStart m C p)=decide (readBit xs p.2.2.1=false)
        rw [← h.length_eq]
        change readBit (norStep xs (p.2.2.1,p.2.2.1)) xs.length=_
        rw [norStep_read_output]
        cases readBit xs p.2.2.1 <;> rfl
      · change readBit ys p.2.2.1=decide (readBit xs p.2.2.1=true)
        rw [norStep_read_old xs _ _ (by rw [h.length_eq]; exact choiceReference_lt m C p)]
        cases readBit xs p.2.2.1 <;> rfl
    · change readBit ys (groundReference p b)=b
      rw [norStep_read_old xs _ _ (by rw [h.length_eq]; exact groundReference_lt m C p b)]
      exact h.ground b
  constructor
  · rw [runNor_length,uniformStep_length,h.length_eq]
    simp only [nextContext,setTime,timeStart,refStateCount,refWidth]
    ring
  · intro b
    change readBit (runNor _ xs) (groundReference p b)=b
    rw [runNor_read_old _ xs _ (by rw [h.length_eq]; exact groundReference_lt m C p b)]
    exact h.ground b
  · intro out
    have hr := materializedLayer_read m p ys s (readBit xs p.2.2.1) hlen hread out
    rw [uniformStep_eq_layer,runNor_append,runNor_single]
    rw [show timeStart m (uniformBlockSize m) p+4=ys.length from hlen.symm]
    change readBit (runNor _ ys) (stateReference m C (nextContext p)
      (stateOrdinal m out) (initialBit m p.1 out))=_
    convert hr using 1
    congr 1
    rw [hlen]
    simp [nextContext,setTime,stateReference,timeStart,refStateCount,refWidth,C]

/-- Choice witnesses occupy exactly the first T registers. The four fixed
ground registers have one unique extension in the subsequent 1-in-3 compiler. -/
def initialStore {T : ℕ} (w : Fin T → Bool) : List Bool := List.ofFn w ++ [true,false,false,false]

@[simp] theorem initialStore_length {T : ℕ} (w : Fin T → Bool) : (initialStore w).length=T+4 := by
  simp [initialStore]

theorem initialStore_read {T : ℕ} (w : Fin T → Bool) (i : Fin T) : readBit (initialStore w) i.val=w i := by
  simp [initialStore,readBit,List.getElem?_append_left (show i.val<(List.ofFn w).length by simpa using i.isLt)]

theorem initialStore_represents (m : Machine) (x : Complexity.Bits) (T : ℕ) (w : Fin T → Bool) :
    StoreRepresents m (x,(T,(0,0))) (initialStore w) (encodeWindow m (x.length+T) (initial m x),true) := by
  have hg (b : Bool) : readBit (initialStore w) (groundReference (x,(T,(0,0))) b)=b := by
    cases b <;> simp [initialStore,readBit,groundReference,List.getElem?_append_right]
  constructor
  · simp [timeStart]
  · exact hg
  · intro out
    simp only [stateReference,↓reduceIte]
    rw [hg]
    exact initialBit_correct m x out

end PlanarHom.CountingCookLevin
