import PlanarHom.RadialPottsMachinePrimitives

/-! Unconditional real TM2 compilers for each numeric radial endpoint. -/
namespace PlanarHom.RadialPotts.Numeric
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
variable {A : Type} {ea : BitEncoding A}

 theorem fp_whiteName {k e r i : A → ℕ} (hk : FP ea BitEncoding.nat k)
    (he : FP ea BitEncoding.nat e) (hr : FP ea BitEncoding.nat r) (hi : FP ea BitEncoding.nat i) :
    FP ea BitEncoding.nat (fun x => whiteName (k x) (e x) (r x) (i x)) :=
  (fp_add (fp_add (fp_mul (fp_mul (fp_const ea BitEncoding.nat 4) (fp_mul hk hk)) he)
    (fp_mul (fp_const ea BitEncoding.nat 4) (fp_mul hr hr))) hi).congr
      (fun _ => by simp only [whiteName,pow_two])

 theorem fp_switchedName {k e r i : A → ℕ} (hk : FP ea BitEncoding.nat k)
    (he : FP ea BitEncoding.nat e) (hr : FP ea BitEncoding.nat r) (hi : FP ea BitEncoding.nat i) :
    FP ea BitEncoding.nat (fun x => switchedName (k x) (e x) (r x) (i x)) := by
  have h0 := fp_const ea BitEncoding.nat 0
  have h1 := fp_const ea BitEncoding.nat 1
  have hp := fp_and (fp_eq hi h0) (fp_lt (fp_add hr h1) hk)
  have hq := fp_and (fp_eq hi h1) (fp_lt h0 hr)
  exact (hp.ite (fp_whiteName hk he (fp_add hr h1) h1)
    (hq.ite (fp_whiteName hk he (fp_sub hr h1) h0) (fp_whiteName hk he hr hi))).congr
      (fun x => by simp [switchedName])

 theorem fp_inputM {p : A → Input} (hp : FP ea inputEncoding p) : FP ea BitEncoding.nat (fun x => (p x).1) :=
  (hp.comp (fp_fst _ _)).comp UnaryNatConversionMachine.fp_conversion
 theorem fp_inputK {p : A → Input} (hp : FP ea inputEncoding p) : FP ea BitEncoding.nat (fun x => (p x).2.1) :=
  ((hp.comp (fp_snd _ _)).comp (fp_fst _ _)).comp UnaryNatConversionMachine.fp_conversion
 theorem fp_inputRotation {p : A → Input} (hp : FP ea inputEncoding p) : FP ea BitEncoding.nat.list (fun x => (p x).2.2) :=
  (hp.comp (fp_snd _ _)).comp (fp_snd _ _)

 theorem fp_portName {p : A → Input} {e s a : A → ℕ} (hp : FP ea inputEncoding p)
    (he : FP ea BitEncoding.nat e) (hs : FP ea BitEncoding.nat s) (ha : FP ea BitEncoding.nat a) :
    FP ea BitEncoding.nat (fun x => portName (p x) (e x) (s x) (a x)) := by
  have hm := fp_inputM hp
  have hk := fp_inputK hp
  have h1 := fp_const ea BitEncoding.nat 1
  have h2 := fp_const ea BitEncoding.nat 2
  have hi := fp_add (fp_mul h2 he) (fp_div hs h2)
  have ho := fp_eq (fp_mod hs h2) h1
  have hd := ho.ite hi (fp_natGetD (fp_inputRotation hp) hi)
  have hl := ho.ite ha (fp_sub (fp_sub hk h1) ha)
  have hbase := fp_mul hm (fp_mul (fp_const ea BitEncoding.nat 4) (fp_mul hk hk))
  exact (fp_add (fp_add hbase (fp_mul hk hd)) hl).congr (fun x => by simp [portName,pow_two])

 def edgeEncoding : BitEncoding (ℕ×(ℕ×ℕ)) := BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)

 theorem fp_longEntry {p : A → Input} {e r s a : A → ℕ} (hp : FP ea inputEncoding p)
    (he : FP ea BitEncoding.nat e) (hr : FP ea BitEncoding.nat r)
    (hs : FP ea BitEncoding.nat s) (ha : FP ea BitEncoding.nat a) :
    FP ea edgeEncoding (fun x => longEntry (p x) (e x) (r x) (s x) (a x)) := by
  have hk := fp_inputK hp
  have h1 := fp_const ea BitEncoding.nat 1
  have h2 := fp_const ea BitEncoding.nat 2
  have hr1 := fp_add hr h1
  have hidx := fp_add (fp_mul hs (fp_add (fp_mul h2 hr) h1)) (fp_mul h2 ha)
  have hidx1 := fp_add (fp_add (fp_mul hs (fp_add (fp_mul h2 hr1) h1)) (fp_mul h2 ha)) h1
  have hsrc := fp_whiteName hk he hr hidx
  have hdst := (fp_lt hr1 hk).ite (fp_whiteName hk he hr1 hidx1) (fp_portName hp he hs ha)
  exact (hsrc.pair (hdst.pair (fp_const ea BitEncoding.nat 0))).congr (fun x => by simp [longEntry])

 theorem fp_shortEntry {k e r j : A → ℕ} (hk : FP ea BitEncoding.nat k)
    (he : FP ea BitEncoding.nat e) (hr : FP ea BitEncoding.nat r) (hj : FP ea BitEncoding.nat j) (b : Bool) :
    FP ea edgeEncoding (fun x => shortEntry (k x) (e x) (r x) (j x) b) := by
  have h1 := fp_const ea BitEncoding.nat 1
  have h2 := fp_const ea BitEncoding.nat 2
  have hj2 := fp_mul h2 hj
  have hj1 := fp_add hj2 h1
  cases b
  · exact ((fp_switchedName hk he hr hj2).pair
      ((fp_switchedName hk he hr hj1).pair h1)).congr (fun _ => rfl)
  · have hn := fp_add (fp_mul (fp_const ea BitEncoding.nat 8) hr) (fp_const ea BitEncoding.nat 4)
    exact ((fp_whiteName hk he hr hj1).pair
      ((fp_whiteName hk he hr (fp_mod (fp_add hj2 h2) hn)).pair h1)).congr (fun _ => rfl)
end PlanarHom.RadialPotts.Numeric
