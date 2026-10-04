import PlanarHom.PottsCoefficientPrograms

/-! NEW reconstruction: the total row-major two-stage rational recovery
program for the radial Potts reduction. n,m are unary; answers use the original
fixed rational basis. Every dynamic power is bounded by these actual headers. -/
noncomputable section
namespace PlanarHom.PottsTwoStageMachines
open Complexity PairProjectionMachines

abbrev Input := ℕ × (ℕ × List ℚ)
def basis := PottsCoefficientPrograms.basis
def fieldCode := numberFieldEncoding basis
def inputEncoding := BitEncoding.unaryNat.prod (BitEncoding.unaryNat.prod fieldCode.list)
def rowEncoding := inputEncoding.prod BitEncoding.nat

def rowPower (δ : ℚ) (p : Input) (k : ℕ) : ℚ := δ^(min p.1 (k+1))

def edgeSample (δ : ℚ) (p : Input) (k l : ℕ) : ℚ × ℚ :=
  let a:=rowPower δ p k
  let r:=min (p.2.1+1) (l+1)
  ((1+a)^r-1,a^p.1*p.2.2.getD (k*(p.2.1+1)+l) 0)

def edgeTable (δ : ℚ) (p : Input) (k : ℕ) : List (ℚ × ℚ) :=
  (List.range (p.2.1+1)).map (edgeSample δ p k)

def rowValue (δ v₀ : ℚ) (p : Input) (k : ℕ) : ℚ :=
  MaterializedPolynomialInterpolationMachines.recover v₀ (edgeTable δ p k)

def colorRow (δ v₀ : ℚ) (p : Input) (k : ℕ) : ℚ × ℚ :=
  ((rowPower δ p k)^2,rowValue δ v₀ p k)

def colorTable (δ v₀ : ℚ) (p : Input) : List (ℚ × ℚ) :=
  (0,0)::(List.range p.1).map (colorRow δ v₀ p)

def recover (δ Q₀ v₀ : ℚ) (p : Input) : ℚ :=
  MaterializedPolynomialInterpolationMachines.recover Q₀ (colorTable δ v₀ p)

theorem fp_rowPower (δ : ℚ) : FP rowEncoding fieldCode (fun p => rowPower δ p.1 p.2) := by
  have hp := fp_fst inputEncoding BitEncoding.nat
  have hn := hp.comp (fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list))
  have hk := (fp_snd inputEncoding BitEncoding.nat).comp BinaryArithmetic.fp_successor
  have hb := (hn.pair hk).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  exact hb.comp (FixedPowerMachines.fp_power basis δ)

theorem fp_edgeSample (δ : ℚ) : FP (rowEncoding.prod BitEncoding.nat)
    (fieldCode.prod fieldCode) (fun p => edgeSample δ p.1.1 p.1.2 p.2) := by
  let inp := rowEncoding.prod BitEncoding.nat
  have hr := fp_fst rowEncoding BitEncoding.nat
  have hl := fp_snd rowEncoding BitEncoding.nat
  have hp := hr.comp (fp_fst inputEncoding BitEncoding.nat)
  have hk := hr.comp (fp_snd inputEncoding BitEncoding.nat)
  have hn := hp.comp (fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list))
  have hma := hp.comp (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list))
  have hm := hma.comp (fp_fst BitEncoding.unaryNat fieldCode.list)
  have ha := hma.comp (fp_snd BitEncoding.unaryNat fieldCode.list)
  have hmp := (hm.pair (fp_const inp BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add
  have hlp := hl.comp BinaryArithmetic.fp_successor
  have he := (hmp.pair hlp).comp (show FP (BitEncoding.unaryNat.prod BitEncoding.nat)
    BitEncoding.unaryNat (fun p => min p.1 p.2) from ⟨BoundedUnaryMachines.computer⟩)
  have hd := hr.comp (fp_rowPower δ)
  have hone := fp_const inp fieldCode (1:ℚ)
  have hbase := (hone.pair hd).comp (FixedFieldArithmetic.fp_addition basis)
  have hpow := (he.pair hbase).comp (MaterializedPowerMachines.fp_power basis)
  have hnode := (hpow.pair hone).comp (FixedFieldArithmetic.fp_subtraction basis)
  have hnorm := (hn.pair hd).comp (MaterializedPowerMachines.fp_power basis)
  have hmb := hmp.comp UnaryNatConversionMachine.fp_conversion
  have hoff := (hk.pair hmb).comp BinaryArithmetic.fp_multiplication
  have hindex := (hoff.pair hl).comp BinaryArithmetic.fp_addition
  have hanswer := (hindex.pair ha).comp
    (MaterializedPolynomialCoefficientMachines.fp_coefficientLookup basis)
  exact hnode.pair ((hnorm.pair hanswer).comp (FixedFieldArithmetic.fp_multiplication basis))

theorem fp_edgeTable (δ : ℚ) : FP rowEncoding (fieldCode.prod fieldCode).list
    (fun p => edgeTable δ p.1 p.2) := by
  have hp := fp_fst inputEncoding BitEncoding.nat
  have hma := hp.comp (fp_snd BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list))
  have hm := hma.comp (fp_fst BitEncoding.unaryNat fieldCode.list)
  have hs := (hm.pair (fp_const rowEncoding BitEncoding.unaryNat 1)).comp UnaryPolynomialMachines.fp_add
  have hrange := (UnaryRangeMachines.fp_range.comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n => List.reverse_reverse (List.range n))
  exact ((fp_id rowEncoding).pair (hs.comp hrange)).comp
    (ListContextMachines.fp_mapWithContext rowEncoding BitEncoding.nat (fieldCode.prod fieldCode)
      (fun p => edgeSample δ p.1.1 p.1.2 p.2) (fp_edgeSample δ))

theorem fp_rowValue (δ v₀ : ℚ) : FP rowEncoding fieldCode (fun p => rowValue δ v₀ p.1 p.2) :=
  (fp_edgeTable δ).comp (MaterializedPolynomialInterpolationMachines.fp_recover basis v₀)

theorem fp_colorRow (δ v₀ : ℚ) : FP rowEncoding (fieldCode.prod fieldCode)
    (fun p => colorRow δ v₀ p.1 p.2) := by
  have hd := fp_rowPower δ
  have hsq := (hd.pair hd).comp (FixedFieldArithmetic.fp_multiplication basis)
  exact (hsq.pair (fp_rowValue δ v₀)).congr (fun p => by simp [colorRow,pow_two])

theorem fp_colorTable (δ v₀ : ℚ) : FP inputEncoding (fieldCode.prod fieldCode).list
    (colorTable δ v₀) := by
  have hn := fp_fst BitEncoding.unaryNat (BitEncoding.unaryNat.prod fieldCode.list)
  have hrange := (UnaryRangeMachines.fp_range.comp
    (ListReverseMachines.fp_reverse BitEncoding.nat)).congr (fun n => List.reverse_reverse (List.range n))
  have hmap := ((fp_id inputEncoding).pair (hn.comp hrange)).comp
    (ListContextMachines.fp_mapWithContext inputEncoding BitEncoding.nat (fieldCode.prod fieldCode)
      (fun p => colorRow δ v₀ p.1 p.2) (fp_colorRow δ v₀))
  exact ((fp_const inputEncoding (fieldCode.prod fieldCode) (0,0)).pair hmap).comp
    (ListMutationMachines.fp_cons (fieldCode.prod fieldCode))

/-- An unconditional total machine; exact sample equations are used only by
its semantic correctness theorem, never as a cost or program assumption. -/
theorem fp_recover (δ Q₀ v₀ : ℚ) : FP inputEncoding fieldCode (recover δ Q₀ v₀) :=
  (fp_colorTable δ v₀).comp (MaterializedPolynomialInterpolationMachines.fp_recover basis Q₀)
end PlanarHom.PottsTwoStageMachines
