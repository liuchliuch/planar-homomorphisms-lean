import PlanarHom.CountingCookLevinLayerBridge

/-! Every actual register address is in the materialized tape, including the
initial grounded constants and the single choice-complement gate. -/
noncomputable section
open Classical
namespace PlanarHom.CountingCookLevin
open SingleTapeNondeterministic

theorem uniformBlockSize_pos (m : Machine) : 0<uniformBlockSize m := by simp [uniformBlockSize]

theorem groundReference_lt (m : Machine) (C : ℕ) (p : RefInput) (b : Bool) :
    groundReference p b<timeStart m C p := by
  cases b <;> simp [groundReference,timeStart] <;> omega

theorem choiceReference_lt (m : Machine) (C : ℕ) (p : RefInput) : p.2.2.1<timeStart m C p := by
  have h := Nat.mul_le_mul_right p.2.2.1 (show 1≤4*(1+C*refStateCount m p) by omega)
  simp only [Nat.one_mul] at h
  simp only [timeStart]
  omega

theorem stateReference_lt (m : Machine) (C : ℕ) (hC : 0<C) (p : RefInput) (slot : ℕ) (b : Bool)
    (hs : slot<refStateCount m p) : stateReference m C p slot b<timeStart m C p := by
  unfold stateReference
  split
  · exact groundReference_lt m C p b
  · rename_i ht
    have hpred : p.2.2.1-1+1=p.2.2.1 := by omega
    have hCpred : C-1+1=C := by omega
    have hm := Nat.mul_le_mul_left (4*C) (show slot+1≤refStateCount m p by omega)
    have hextra : 4+4*C*slot+4*(C-1)<4*(1+C*refStateCount m p) := by nlinarith
    have he : 4*(1+C*refStateCount m p)*p.2.2.1 =
        4*(1+C*refStateCount m p)*(p.2.2.1-1)+4*(1+C*refStateCount m p) := by
      conv_lhs => rw [← hpred]
      ring
    unfold timeStart
    rw [he]
    omega

theorem globalReference_lt (m : Machine) (C : ℕ) (hC : 0<C) (p : RefInput)
    (v : LayerInput m (p.1.length+p.2.1)) : globalReference m C p v<timeStart m C p+4 := by
  rcases v with (s | b) | b
  · have h := stateReference_lt m C hC p (stateOrdinal m s) (initialBit m p.1 s)
      (show stateOrdinal m s<refStateCount m p from (stateIndexEquiv m _ s).isLt)
    exact h.trans_le (by omega)
  · cases b
    · simp [globalReference]
    · exact (choiceReference_lt m C p).trans_le (by omega)
  · exact (groundReference_lt m C p b).trans_le (by omega)

theorem layer_copyOutput_bound (m : Machine) {L : ℕ} (out : StateBit m L) :
    (stepLayer m out).copyOutput.gates≤uniformBlockSize m := by
  have h := stepLayer_gates_le m out
  rw [Expr.copyOutput_gates]
  unfold uniformBlockSize
  omega

/-- The materialized shared-register layer computes the actual next-state bit. -/
theorem materializedLayer_read (m : Machine) (p : RefInput) (xs : List Bool)
    (s : ReplayState m (p.1.length+p.2.1)) (b : Bool)
    (hlen : xs.length=timeStart m (uniformBlockSize m) p+4)
    (hread : ∀ v,readBit xs (globalReference m (uniformBlockSize m) p v)=layerInputs m s b v)
    (out : StateBit m (p.1.length+p.2.1)) :
    readBit (runNor (Expr.regularLayer ((stateRegisterOrder m (p.1.length+p.2.1)).map (stepLayer m))
      (uniformBlockSize m) xs.length (globalReference m (uniformBlockSize m) p)) xs)
      (xs.length+4*uniformBlockSize m*stateOrdinal m out+4*(uniformBlockSize m-1))=
        stateBits m (windowStep m s b) out := by
  have hC : ∀ e∈(stateRegisterOrder m (p.1.length+p.2.1)).map (stepLayer m),
      e.copyOutput.gates≤uniformBlockSize m := by
    intro e he
    obtain ⟨o,_,rfl⟩ := List.mem_map.mp he
    exact layer_copyOutput_bound m o
  have hρ (v : LayerInput m (p.1.length+p.2.1)) :
      globalReference m (uniformBlockSize m) p v<xs.length := by
    rw [hlen]
    exact globalReference_lt m _ (uniformBlockSize_pos m) p v
  have hl := Expr.regularLayer_correct
    ((stateRegisterOrder m (p.1.length+p.2.1)).map (stepLayer m))
    (uniformBlockSize m) (globalReference m (uniformBlockSize m) p) xs hC hρ
  have hs : stateOrdinal m out<stateRegisterCount m (p.1.length+p.2.1) :=
    (stateIndexEquiv m _ out).isLt
  have he := congrArg (fun l : List Bool => l[stateOrdinal m out]?) hl
  simp only [Expr.layerOutputs,List.length_map,stateRegisterOrder_length,List.getElem?_map,
    List.getElem?_range,hs,↓reduceIte,Option.map_some,stateRegisterOrder_get] at he
  have hev : (stepLayer m out).eval (fun v => readBit xs (globalReference m (uniformBlockSize m) p v))=
      stateBits m (windowStep m s b) out := by
    rw [(stepLayer m out).eval_congr _ _ hread]
    exact stepLayer_correct m s b out
  exact (Option.some.inj he).trans hev

end PlanarHom.CountingCookLevin
