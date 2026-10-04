import PlanarHom.CoefficientConvolutionMachines

/-! Generic actual polynomial evaluation with runtime algebra context. Dynamic
products, sums, and multiplication are supplied as genuine FP programs, never
as field assumptions or arithmetic-cost oracles. -/
noncomputable section
namespace PlanarHom.RuntimePolynomialEvaluationMachines
open Complexity PairProjectionMachines
variable {A C : Type}

theorem fp_replicate (ea : BitEncoding A) :
    FP (BitEncoding.unaryNat.prod ea) ea.list (fun p : ℕ × A => List.replicate p.1 p.2) := by
  have hn := fp_fst BitEncoding.unaryNat ea
  have ha := fp_snd BitEncoding.unaryNat ea
  have hr := hn.comp UnaryArithmeticMachines.fp_range
  have hm := (ha.pair hr).comp (ListContextMachines.fp_mapWithContext ea BitEncoding.nat ea
    Prod.fst (fp_fst ea BitEncoding.nat))
  exact hm.congr (fun p => by simp)

def power (one : A) (product : C → A → List A → A) (p : C × (ℕ × A)) : A :=
  product p.1 one (List.replicate p.2.1 p.2.2)

theorem fp_power (ea : BitEncoding A) (ec : BitEncoding C) (one : A)
    (product : C → A → List A → A)
    (hp : FP (ec.prod (ea.prod ea.list)) ea (fun p => product p.1 p.2.1 p.2.2)) :
    FP (ec.prod (BitEncoding.unaryNat.prod ea)) ea (power one product) := by
  let ei := ec.prod (BitEncoding.unaryNat.prod ea)
  have hc := fp_fst ec (BitEncoding.unaryNat.prod ea)
  have hr := (fp_snd ec (BitEncoding.unaryNat.prod ea)).comp (fp_replicate ea)
  exact (hc.pair ((fp_const ei ea one).pair hr)).comp hp

def cappedTerm (mul : C → A → A → A) (pow : C → ℕ → A → A)
    (p : (C × (A × ℕ)) × (A × ℕ)) : A :=
  mul p.1.1 p.2.1 (pow p.1.1 (min p.1.2.2 p.2.2) p.1.2.1)

theorem fp_cappedTerm (ea : BitEncoding A) (ec : BitEncoding C)
    (mul : C → A → A → A) (pow : C → ℕ → A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2))
    (hpow : FP (ec.prod (BitEncoding.unaryNat.prod ea)) ea (fun p => pow p.1 p.2.1 p.2.2)) :
    FP ((ec.prod (ea.prod BitEncoding.unaryNat)).prod (ea.prod BitEncoding.nat)) ea
      (cappedTerm mul pow) := by
  let ect := ec.prod (ea.prod BitEncoding.unaryNat)
  let ei := ea.prod BitEncoding.nat
  have hl := fp_fst ect ei
  have hr := fp_snd ect ei
  have hc := hl.comp (fp_fst ec (ea.prod BitEncoding.unaryNat))
  have ht := hl.comp (fp_snd ec (ea.prod BitEncoding.unaryNat))
  have hb := ht.comp (fp_fst ea BitEncoding.unaryNat)
  have hn := ht.comp (fp_snd ea BitEncoding.unaryNat)
  have ha := hr.comp (fp_fst ea BitEncoding.nat)
  have hi := hr.comp (fp_snd ea BitEncoding.nat)
  have hj := (hn.pair hi).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  have hp := (hc.pair (hj.pair hb)).comp hpow
  exact (hc.pair (ha.pair hp)).comp hmul

def evaluate (mul : C → A → A → A) (pow : C → ℕ → A → A)
    (sum : C → List A → A) (p : C × (A × List A)) : A :=
  sum p.1 (p.2.2.zipIdx.map (fun q => mul p.1 q.1 (pow p.1 q.2 p.2.1)))

theorem fp_evaluate (ea : BitEncoding A) (ec : BitEncoding C)
    (mul : C → A → A → A) (pow : C → ℕ → A → A) (sum : C → List A → A)
    (hmul : FP (ec.prod (ea.prod ea)) ea (fun p => mul p.1 p.2.1 p.2.2))
    (hpow : FP (ec.prod (BitEncoding.unaryNat.prod ea)) ea (fun p => pow p.1 p.2.1 p.2.2))
    (hsum : FP (ec.prod ea.list) ea (fun p => sum p.1 p.2)) :
    FP (ec.prod (ea.prod ea.list)) ea (evaluate mul pow sum) := by
  have hc := fp_fst ec (ea.prod ea.list)
  have ht := fp_snd ec (ea.prod ea.list)
  have hb := ht.comp (fp_fst ea ea.list)
  have hcs := ht.comp (fp_snd ea ea.list)
  have hn := hcs.comp (ListUnaryLengthMachine.fp_length ea)
  have hidx := hcs.comp (ListIndexMachines.fp_zipIdx ea)
  have hm := ((hc.pair (hb.pair hn)).pair hidx).comp
    (ListContextMachines.fp_mapWithContext (ec.prod (ea.prod BitEncoding.unaryNat))
      (ea.prod BitEncoding.nat) ea (cappedTerm mul pow) (fp_cappedTerm ea ec mul pow hmul hpow))
  apply ((hc.pair hm).comp hsum).congr
  intro p
  change sum p.1 (p.2.2.zipIdx.map (fun q => cappedTerm mul pow ((p.1,(p.2.1,p.2.2.length)),q))) = _
  unfold evaluate
  congr 1
  apply List.map_congr_left
  intro q hq
  have hi : q.2 < p.2.2.length := by simpa using List.snd_lt_of_mem_zipIdx hq
  simp only [cappedTerm, min_eq_right (Nat.le_of_lt hi)]

end PlanarHom.RuntimePolynomialEvaluationMachines
