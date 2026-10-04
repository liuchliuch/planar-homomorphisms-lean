import PlanarHom.DependentTargetAggregation
import PlanarHom.DependentFieldEqualityMachines
import PlanarHom.ContextPairTestMachines
import PlanarHom.CrossFieldProductClasses

/-! Actual heterogeneous-field collision testing without forming a compositum. -/
noncomputable section
namespace PlanarHom.CrossFieldCollisionMachines
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives
open scoped BigOperators
variable {L X : Type} [Field L] [Algebra ℚ L] [DecidableEq L]
variable {sourceDimension t : ℕ} (sourceBasis : Module.Basis (Fin sourceDimension) ℚ L)
variable (ex : BitEncoding X) (K : X → Type) [∀ x, Field (K x)] [∀ x, Algebra ℚ (K x)]
variable [∀ x, DecidableEq (K x)]
variable (dimension : X → ℕ) (basis : ∀ x, Module.Basis (Fin (dimension x)) ℚ (K x))
variable (inclusion : ∀ x, L →+* K x) (B : ∀ x, Fin t → K x)

def bad (p : X × ℕ) (a b : L × List ℕ) : Bool :=
  decide (a.1 ≠ 0 ∧ a.1 = b.1 ∧
    (∏ i, B p.1 i ^ min p.2 (a.2.getD i.val 0)) ≠
      (∏ i, B p.1 i ^ min p.2 (b.2.getD i.val 0)))

abbrev Input (L X : Type) (t : ℕ) := (X × ℕ) × (Fin t → L)

def test (p : Input L X t) : Bool :=
  !(ContextPairTestMachines.anyPair (bad K B) (p.1, SourceExponentRepresentatives.products p.2 p.1.2))

theorem test_eq_true_iff (p : Input L X t) : test K B p = true ↔
    SourceExponentRepresentatives.CrossCompatibleAt p.2 (B p.1.1) p.1.2 := by
  rw [test, Bool.not_eq_true', ContextPairTestMachines.anyPair_eq_false_iff]
  constructor
  · intro h xs hx ys hy hz he
    have hh := h (ExponentProductSemantics.value p.2 xs,xs) (List.mem_map.mpr ⟨xs,hx,rfl⟩)
      (ExponentProductSemantics.value p.2 ys,ys) (List.mem_map.mpr ⟨ys,hy,rfl⟩)
    have ht : (∏ i, B p.1.1 i ^ min p.1.2 (xs.getD i.val 0)) =
        (∏ i, B p.1.1 i ^ min p.1.2 (ys.getD i.val 0)) := by
      by_contra hne
      exact (of_decide_eq_false hh) ⟨hz,he,hne⟩
    simpa only [DependentMonomialMachines.clipped_eq (B p.1.1) p.1.2 xs hx,
      DependentMonomialMachines.clipped_eq (B p.1.1) p.1.2 ys hy] using ht
  · intro h a ha b hb
    obtain ⟨xs,hx,rfl⟩ := List.mem_map.mp ha
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hb
    simp only [bad, decide_eq_false_iff_not, not_and]
    intro hz he
    rw [DependentMonomialMachines.clipped_eq (B p.1.1) p.1.2 xs hx,
      DependentMonomialMachines.clipped_eq (B p.1.1) p.1.2 ys hy]
    exact not_not.mpr (h xs hx ys hy hz he)

variable (c : ℕ) (hc : ∀ x, dimension x ≤ c)
variable (hpresentation : FP ex BitEncoding.rat.list
  (fun x => UniformFieldPresentationHeights.presentationList (basis x)))
variable (hmul : FP (DependentFieldCodecs.pair ex (DependentFieldListMachines.fieldEncoding K dimension basis))
  (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
  (fun s : Σ x, K x × K x => ⟨s.1,s.2.1*s.2.2⟩))
variable (hinclusion : FP (ex.prod (numberFieldEncoding sourceBasis))
  (DependentFieldCodecs.sigma ex (DependentFieldListMachines.fieldEncoding K dimension basis))
  (fun p => ⟨p.1,inclusion p.1 p.2⟩))
variable (hB : FP ex (DependentFieldCodecs.sigma ex
  (fun x => (DependentFieldListMachines.fieldEncoding K dimension basis x).vector t)) (fun x => ⟨x,B x⟩))

include hc hpresentation hmul hinclusion hB in
theorem fp_bad : FP (((ex.prod BitEncoding.unaryNat).prod
    (SourceExponentRepresentatives.rowEncoding sourceBasis)).prod (SourceExponentRepresentatives.rowEncoding sourceBasis))
    BitEncoding.bool (fun p => bad K B p.1.1 p.1.2 p.2) := by
  let e := DependentFieldListMachines.fieldEncoding K dimension basis
  let er := SourceExponentRepresentatives.rowEncoding sourceBasis
  let ec := ex.prod BitEncoding.unaryNat
  let ed := (ec.prod er).prod er
  have hp := fp_fst (ec.prod er) er
  have hcontext := hp.comp (fp_fst ec er)
  have hx := hcontext.comp (fp_fst ex BitEncoding.unaryNat)
  have hm := hcontext.comp (fp_snd ex BitEncoding.unaryNat)
  have ha := hp.comp (fp_snd ec er)
  have hb := fp_snd (ec.prod er) er
  have hμ := ha.comp (fp_fst (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hν := hb.comp (fp_fst (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hra := ha.comp (fp_snd (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hrb := hb.comp (fp_snd (numberFieldEncoding sourceBasis) BitEncoding.nat.list)
  have hone := DependentTargetAggregation.fp_one sourceBasis ex K dimension basis inclusion hinclusion
  have hη := DependentMonomialMachines.fp_monomial ex K dimension basis ed (fun p => p.1.1.1)
    c hc hpresentation hmul hone (fun p => B p.1.1.1) (fun p => p.1.1.2) (fun p => p.1.2.2)
    (hx.comp hB) hm hra
  have hθ := DependentMonomialMachines.fp_monomial ex K dimension basis ed (fun p => p.1.1.1)
    c hc hpresentation hmul hone (fun p => B p.1.1.1) (fun p => p.1.1.2) (fun p => p.2.2)
    (hx.comp hB) hm hrb
  have hzero := (hμ.pair (fp_const ed (numberFieldEncoding sourceBasis) 0)).comp (FixedFieldArithmetic.fp_equality sourceBasis)
  have hse := (hμ.pair hν).comp (FixedFieldArithmetic.fp_equality sourceBasis)
  have hte := (DependentEncodingMachines.fp_pair ex e e hη hθ).comp
    (DependentFieldEqualityMachines.fp_equality ex K dimension basis c hc)
  have hnz := hzero.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have htn := hte.comp (fp_bool_unary BitEncoding.bool Bool.not)
  have hlast := (hse.pair htn).comp (fp_bool_gate (fun p => p.1 && p.2))
  exact ((hnz.pair hlast).comp (fp_bool_gate (fun p => p.1 && p.2))).congr (fun p => by simp [bad])

include hc hpresentation hmul hinclusion hB in
theorem fp_test : FP ((ex.prod BitEncoding.unaryNat).prod ((numberFieldEncoding sourceBasis).vector t))
    BitEncoding.bool (test K B) := by
  let ea := (numberFieldEncoding sourceBasis).vector t
  have hp := fp_fst (ex.prod BitEncoding.unaryNat) ea
  have hm := hp.comp (fp_snd ex BitEncoding.unaryNat)
  have ha := fp_snd (ex.prod BitEncoding.unaryNat) ea
  have hrows := (hm.pair ha).comp (SourceExponentRepresentatives.fp_products sourceBasis)
  have hany := (hp.pair hrows).comp (ContextPairTestMachines.fp_anyPair _ _ _
    (fp_bad sourceBasis ex K dimension basis inclusion B c hc hpresentation hmul hinclusion hB))
  exact hany.comp (fp_bool_unary BitEncoding.bool Bool.not)

end PlanarHom.CrossFieldCollisionMachines
