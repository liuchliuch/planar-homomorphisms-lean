import PlanarHom.RepresentedProductContracts
import PlanarHom.ListFlattenMachines
import PlanarHom.ListContextMachines

/-! Powers of retained source monomials are computed by bounded word repetition
and the fixed-alphabet product machine. No dynamic fraction-power size claim is
inferred from primitive arithmetic. The exponent is explicitly unary. -/
noncomputable section
open Classical
namespace PlanarHom.RepresentedBit
open Complexity PairProjectionMachines

 def repeatWord (p:ℕ×List ℕ) : List ℕ := (List.range p.1).flatMap (fun _=>p.2)

theorem fp_repeatWord : FP (BitEncoding.unaryNat.prod BitEncoding.nat.list)
    BitEncoding.nat.list repeatWord := by
  have h:=(fp_snd BitEncoding.unaryNat BitEncoding.nat.list).pair
    ((fp_fst BitEncoding.unaryNat BitEncoding.nat.list).comp UnaryRangeMachines.fp_range)
  exact ((h.comp (ListContextMachines.fp_mapWithContext BitEncoding.nat.list BitEncoding.nat
    BitEncoding.nat.list (fun p=>p.1) (fp_fst _ _))).comp
      (ListFlattenMachines.fp_flatten BitEncoding.nat)).congr (fun p=>by
        simp [Function.comp_def,repeatWord,List.flatMap_def])

theorem repeatWord_proper {t:ℕ} (n:ℕ) (w:List ℕ) (hw:properWord t w) :
    properWord t (repeatWord (n,w)) := by
  intro i hi
  obtain ⟨j,hj,hi⟩:=List.mem_flatMap.mp hi
  exact hw i hi

theorem repeatWord_length (n:ℕ) (w:List ℕ) : (repeatWord (n,w)).length=n*w.length := by
  simp [repeatWord,List.length_flatMap]

theorem repeatWord_product {K:Type} [CommMonoid K] {t:ℕ} (A:Fin t→K) (n:ℕ) (w:List ℕ) :
    ((repeatWord (n,w)).map (RepresentedExponentWords.symbol A)).prod=
      ((w.map (RepresentedExponentWords.symbol A)).prod)^n := by
  simp [repeatWord,List.map_flatMap,List.flatMap_def,List.prod_flatten]

def repeatProper {t:ℕ} (p:ℕ×{w:List ℕ//properWord t w}) : {w:List ℕ//properWord t w} :=
  ⟨repeatWord (p.1,p.2.val),repeatWord_proper _ _ p.2.property⟩

theorem fp_repeatProper (t:ℕ) : FP (BitEncoding.unaryNat.prod (wordEncoding t))
    (wordEncoding t) repeatProper := by
  have h:FP (BitEncoding.unaryNat.prod (wordEncoding t))
      (BitEncoding.unaryNat.prod BitEncoding.nat.list) (fun p=>(p.1,p.2.val)):=
    fp_code_view _ _ _ (fun _=>rfl)
  exact (h.comp fp_repeatWord).transportOutput (fun _=>rfl)

variable {K:Type} [CommSemiring K] {P:Presentation K} {t:ℕ} {A:Fin t→K}

def WordProductMachine.power (M:WordProductMachine P A)
    (p:ℕ×{w:List ℕ//properWord t w}) : ValidCode P :=
  ⟨M.run (repeatProper p),M.valid _⟩

theorem WordProductMachine.fp_power (M:WordProductMachine P A) :
    FP (BitEncoding.unaryNat.prod (wordEncoding t)) (validEncoding P) M.power :=
  ((fp_repeatProper t).comp M.fp).transportOutput (fun _=>rfl)

theorem WordProductMachine.power_value (M:WordProductMachine P A)
    (n:ℕ) (w:{w:List ℕ//properWord t w}) :
    validValue P (M.power (n,w))=((w.val.map (RepresentedExponentWords.symbol A)).prod)^n := by
  rw [validValue,WordProductMachine.power,M.value]
  exact repeatWord_product A n w.val

end PlanarHom.RepresentedBit
