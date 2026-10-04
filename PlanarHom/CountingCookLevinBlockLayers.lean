import PlanarHom.CountingCookLevinRegularBlocks

/-! Flattening shared Boolean layers into fixed-size NOR register blocks. -/
namespace PlanarHom.CountingCookLevin
namespace Expr

def regularLayer {V : Type} : List (Expr V) → ℕ → ℕ → (V → ℕ) → NorGates
  | [], _, _, _ => []
  | e::es, C, start, ρ => e.regularBlock C start ρ ++ regularLayer es C (start+4*C) ρ

def layerOutputs (length C start : ℕ) : List ℕ :=
  (List.range length).map (fun i => start+4*C*i+4*(C-1))

theorem regularLayer_length {V : Type} (es : List (Expr V)) (C start : ℕ) (ρ : V → ℕ)
    (hC : ∀ e∈es,e.copyOutput.gates≤C) : (regularLayer es C start ρ).length=C*es.length := by
  induction es generalizing start with
  | nil => simp [regularLayer]
  | cons e es ih =>
    rw [regularLayer,List.length_append,regularBlock_length e C start ρ (hC _ (by simp)),
      ih _ (fun a ha => hC a (by simp [ha])),List.length_cons]
    ring

theorem layerOutputs_cons (n C start : ℕ) :
    layerOutputs (n+1) C start=(start+4*(C-1))::layerOutputs n C (start+4*C) := by
  simp only [layerOutputs,List.range_succ_eq_map,List.map_cons,List.map_map,Function.comp_def,
    Nat.mul_zero,Nat.add_zero]
  congr 1
  apply List.map_congr_left
  intro i _
  simp only [Nat.succ_eq_add_one]
  ring

/-- All emitted output addresses compute their corresponding local templates;
earlier outputs and all old input registers survive later blocks unchanged. -/
theorem regularLayer_correct {V : Type} (es : List (Expr V)) (C : ℕ) (ρ : V → ℕ) (xs : List Bool)
    (hC : ∀ e∈es,e.copyOutput.gates≤C) (hρ : ∀ v,ρ v<xs.length) :
    (layerOutputs es.length C xs.length).map (readBit (runNor (regularLayer es C xs.length ρ) xs)) =
      es.map (fun e => e.eval (fun v => readBit xs (ρ v))) := by
  induction es generalizing xs with
  | nil => rfl
  | cons e es ih =>
    let ys := runNor (e.regularBlock C xs.length ρ) xs
    have hlen : ys.length=xs.length+4*C := by simp [ys,regularBlock_length e C xs.length ρ (hC _ (by simp))]
    have hC' : ∀ a∈es,a.copyOutput.gates≤C := fun a ha => hC a (by simp [ha])
    have hρ' : ∀ v,ρ v<ys.length := fun v => (hρ v).trans_le (by rw [hlen]; omega)
    have hpos : 0<C := by
      have h := hC e (by simp)
      rw [copyOutput_gates] at h
      omega
    have ho : xs.length+4*(C-1)<ys.length := by rw [hlen]; omega
    rw [List.length_cons,layerOutputs_cons,regularLayer,runNor_append,List.map_cons,List.map_cons]
    congr 1
    · change readBit (runNor (regularLayer es C (xs.length+4*C) ρ) ys)
        (xs.length+4*(C-1))=_
      rw [runNor_read_old _ ys _ ho]
      exact regularBlock_correct e C ρ xs (hC _ (by simp)) hρ
    · rw [← hlen]
      change (layerOutputs es.length C ys.length).map
        (readBit (runNor (regularLayer es C ys.length ρ) ys))=_
      rw [ih ys hC' hρ']
      apply List.map_congr_left
      intro a _
      exact a.eval_congr _ _ (fun v => runNor_read_old _ xs _ (hρ v))

end Expr
end PlanarHom.CountingCookLevin
