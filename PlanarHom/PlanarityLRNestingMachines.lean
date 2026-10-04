import PlanarHom.PlanarityLRNesting
import PlanarHom.PlanarityLRReturnMachines

/-! NEW actual FP highest-return selection and side extension. -/
namespace PlanarHom.PlanarityLRDirect
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives Polynomial
open PlanarityLRRawConstraints PlanarityLRConstraints PlanarityParitySolver

abbrev maximumCode := MixedCode.encoding.prod (BitEncoding.bool.prod BitEncoding.nat)
abbrev graphBitsCode := MixedCode.encoding.prod BitEncoding.bool.list

def maximumStep (s : MixedCode × (Bool × ℕ)) (e : ℕ) : MixedCode × (Bool × ℕ) :=
  (s.1,(true,if s.2.1 = false ∨ targetHeight s.1 s.2.2 ≤ targetHeight s.1 e then e else s.2.2))

def maximumState (g : MixedCode) (es : List ℕ) : Bool × ℕ :=
  (es.reverse.foldl maximumStep (g,(false,0))).2

def maximumDecode (s : Bool × ℕ) : Option ℕ := if s.1 then some s.2 else none

theorem maximumFold_graph (es : List ℕ) (s : MixedCode × (Bool × ℕ)) :
    (es.foldl maximumStep s).1 = s.1 := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simpa only [List.foldl_cons,ih,maximumStep]

theorem maximumFold_index (es : List ℕ) (s : MixedCode × (Bool × ℕ)) :
    (es.foldl maximumStep s).2.2 = s.2.2 ∨ (es.foldl maximumStep s).2.2 ∈ es := by
  induction es generalizing s with
  | nil => exact Or.inl rfl
  | cons e es ih =>
    have h := ih (maximumStep s e)
    rcases h with h | h
    · simp only [List.foldl_cons]
      rw [h]
      simp only [maximumStep]
      split_ifs
      · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inl rfl
    · exact Or.inr (List.mem_cons_of_mem _ h)

theorem maximumState_result (g : MixedCode) (es : List ℕ) :
    maximumDecode (maximumState g es) = maximumReturn g es := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    have hg := maximumFold_graph es.reverse (g,(false,0))
    simp only [maximumState,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil]
    simp only [maximumState] at ih
    generalize hs : es.reverse.foldl maximumStep (g,(false,0)) = s at *
    rcases s with ⟨g',flag,k⟩
    change g' = g at hg
    subst g'
    rw [maximumReturn,← ih]
    cases flag <;> simp [maximumDecode,maximumStep]

theorem fp_maximumStep : FP (maximumCode.prod BitEncoding.nat) maximumCode
    (fun p => maximumStep p.1 p.2) := by
  have hs := fp_fst maximumCode BitEncoding.nat
  have hg := hs.comp (fp_fst MixedCode.encoding (BitEncoding.bool.prod BitEncoding.nat))
  have hpair := hs.comp (fp_snd MixedCode.encoding (BitEncoding.bool.prod BitEncoding.nat))
  have hflag := hpair.comp (fp_fst BitEncoding.bool BitEncoding.nat)
  have hk := hpair.comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have he := fp_snd maximumCode BitEncoding.nat
  have hle := (((hg.pair hk).comp fp_targetHeight).pair ((hg.pair he).comp fp_targetHeight)).comp fp_le
  have hnot := hflag.comp (fp_bool_unary BitEncoding.bool not)
  have htest : FP (maximumCode.prod BitEncoding.nat) BitEncoding.bool
      (fun p => decide (p.1.2.1 = false ∨ targetHeight p.1.1 p.1.2.2 ≤ targetHeight p.1.1 p.2)) :=
    ((hnot.pair hle).comp (fp_bool_gate (fun p => p.1 || p.2))).congr (fun p => by
      change ((!p.1.2.1) || decide (targetHeight p.1.1 p.1.2.2 ≤ targetHeight p.1.1 p.2)) =
        decide (p.1.2.1 = false ∨ targetHeight p.1.1 p.1.2.2 ≤ targetHeight p.1.1 p.2)
      cases p.1.2.1 <;> simp)
  exact hg.pair ((fp_const _ BitEncoding.bool true).pair (htest.ite he hk))

theorem fp_maximumState : FP (MixedCode.encoding.prod BitEncoding.nat.list)
    (BitEncoding.bool.prod BitEncoding.nat) (fun p => maximumState p.1 p.2) := by
  have hfold := ListFoldMachines.fp_foldl BitEncoding.nat maximumCode maximumStep fp_maximumStep X (by
    intro s es k _
    have hg := maximumFold_graph (es.take k) s
    have hi := maximumFold_index (es.take k) s
    have hb : (BitEncoding.nat.encode (((es.take k).foldl maximumStep s).2.2)).length ≤
        (BitEncoding.nat.encode s.2.2).length + (BitEncoding.nat.list.encode es).length := by
      rcases hi with hi | hi
      · rw [hi]
        omega
      · have hh := encoded_element_le BitEncoding.nat (List.mem_of_mem_take hi)
        omega
    simp only [Polynomial.eval_X,maximumCode,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
    rw [hg]
    omega)
  have hg := fp_fst MixedCode.encoding BitEncoding.nat.list
  have hs := hg.pair ((fp_const _ BitEncoding.bool false).pair (fp_const _ BitEncoding.nat 0))
  have he := (fp_snd MixedCode.encoding BitEncoding.nat.list).comp (ListReverseMachines.fp_reverse BitEncoding.nat)
  exact (((hs.pair he).comp hfold).comp (fp_snd MixedCode.encoding (BitEncoding.bool.prod BitEncoding.nat)))

theorem fp_edgeSide : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.bool
    (fun p => edgeSide p.1.1 p.1.2 p.2) := by
  have hc := fp_fst graphBitsCode BitEncoding.nat
  have hg := hc.comp (fp_fst MixedCode.encoding BitEncoding.bool.list)
  have hb := hc.comp (fp_snd MixedCode.encoding BitEncoding.bool.list)
  have he := fp_snd graphBitsCode BitEncoding.nat
  have hr := (hg.pair he).comp fp_returns
  have hm := (hg.pair hr).comp fp_maximumState
  have hflag : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.bool
      (fun p => decide ((maximumState p.1.1 (returns p.1.1 p.2)).1 = true)) :=
    (hm.comp (fp_fst BitEncoding.bool BitEncoding.nat)).congr (fun p => by simp)
  have hk := hm.comp (fp_snd BitEncoding.bool BitEncoding.nat)
  have hlookup : FP (graphBitsCode.prod BitEncoding.nat) BitEncoding.bool
      (fun p => bitSide p.1.2 (maximumState p.1.1 (returns p.1.1 p.2)).2) :=
    ((hb.pair hk).comp (PfaffianList.fp_at BitEncoding.bool false)).congr (fun p => by
      simp [bitSide,PfaffianList.lookup,List.getD_eq_getElem?_getD])
  exact (hflag.ite hlookup (fp_const _ BitEncoding.bool true)).congr (fun p => by
    rw [edgeSide,← maximumState_result]
    unfold maximumDecode
    split_ifs <;> rfl)

end PlanarHom.PlanarityLRDirect
