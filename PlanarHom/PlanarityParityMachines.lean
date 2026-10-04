import PlanarHom.PlanarityParityMaterialized
import PlanarHom.ListDecompositionMachines

/-! NEW actual typed machines for parity elimination and substitution. -/
namespace PlanarHom.PlanarityParitySolver
open Complexity PairProjectionMachines ArithmeticCircuitPrimitives ListFlattenMachines Polynomial

abbrev natCode := BitEncoding.nat
abbrev constraintCode := natCode.prod (natCode.prod BitEncoding.bool)
abbrev assignmentCode := (natCode.prod BitEncoding.bool).list
abbrev forwardCode := (constraintCode.list.prod constraintCode.list).prod BitEncoding.bool

def lookupStep (s : ℕ × Bool) (p : ℕ × Bool) : ℕ × Bool :=
  (s.1,if s.1 = p.1 then p.2 else s.2)

def lookupD : Assignment → ℕ → Bool → Bool
  | [], _, d => d
  | (u,b)::xs, v, d => if v = u then b else lookupD xs v d

theorem lookupD_false (xs : Assignment) (v : ℕ) : lookupD xs v false = lookup xs v := by
  induction xs with
  | nil => rfl
  | cons p xs ih => rcases p with ⟨u,b⟩; simp [lookupD,lookup,ih]

theorem lookupStep_reverse (xs : Assignment) (v : ℕ) (b : Bool) :
    xs.reverse.foldl lookupStep (v,b) = (v,lookupD xs v b) := by
  induction xs generalizing b with
  | nil => rfl
  | cons p xs ih =>
    rcases p with ⟨u,c⟩
    simp [List.reverse_cons,List.foldl_append,ih,lookupStep,lookupD]

theorem fp_lookupStep : FP ((natCode.prod BitEncoding.bool).prod (natCode.prod BitEncoding.bool))
    (natCode.prod BitEncoding.bool) (fun p => lookupStep p.1 p.2) := by
  have hl := fp_fst (natCode.prod BitEncoding.bool) (natCode.prod BitEncoding.bool)
  have hr := fp_snd (natCode.prod BitEncoding.bool) (natCode.prod BitEncoding.bool)
  have hkey := hl.comp (fp_fst natCode BitEncoding.bool)
  have htest := (hkey.pair (hr.comp (fp_fst natCode BitEncoding.bool))).comp NatListSumMachines.fp_equal
  exact hkey.pair (htest.ite (hr.comp (fp_snd natCode BitEncoding.bool))
    (hl.comp (fp_snd natCode BitEncoding.bool)))

theorem lookupStep_fold_first (xs : Assignment) (s : ℕ × Bool) :
    (xs.foldl lookupStep s).1 = s.1 := by
  induction xs generalizing s with
  | nil => rfl
  | cons p xs ih => simpa only [List.foldl_cons,ih,lookupStep]

theorem fp_lookup : FP (natCode.prod assignmentCode) BitEncoding.bool (fun p => lookup p.2 p.1) := by
  have hf := ListFoldMachines.fp_foldl (natCode.prod BitEncoding.bool) (natCode.prod BitEncoding.bool)
    lookupStep fp_lookupStep X (by
      intro s xs i _
      simp only [Polynomial.eval_X,BitEncoding.prod_length,BitEncoding.bool,List.length_singleton]
      rw [lookupStep_fold_first]
      omega)
  have hs := (fp_fst natCode assignmentCode).pair (fp_const _ BitEncoding.bool false)
  have hx := (fp_snd natCode assignmentCode).comp (ListReverseMachines.fp_reverse (natCode.prod BitEncoding.bool))
  exact (((hs.pair hx).comp hf).comp (fp_snd natCode BitEncoding.bool)).congr
    (fun p => by
      change (p.2.reverse.foldl lookupStep (p.1,false)).2 = lookup p.2 p.1
      rw [lookupStep_reverse]
      exact lookupD_false p.2 p.1)

theorem fp_substitute : FP (constraintCode.prod constraintCode) constraintCode
    (fun p => substitute p.1.1 p.1.2.1 p.1.2.2 p.2) := by
  have hp := fp_fst constraintCode constraintCode
  have he := fp_snd constraintCode constraintCode
  have hu := hp.comp (fp_fst natCode (natCode.prod BitEncoding.bool))
  have hv := (hp.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_fst natCode BitEncoding.bool)
  have hb := (hp.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_snd natCode BitEncoding.bool)
  have hx := he.comp (fp_fst natCode (natCode.prod BitEncoding.bool))
  have hy := (he.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_fst natCode BitEncoding.bool)
  have ht := (he.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_snd natCode BitEncoding.bool)
  have htx := (hx.pair hu).comp NatListSumMachines.fp_equal
  have hty := (hy.pair hu).comp NatListSumMachines.fp_equal
  have hb₁ := htx.ite hb (fp_const _ BitEncoding.bool false)
  have hb₂ := hty.ite hb (fp_const _ BitEncoding.bool false)
  have hv₁ := (ht.pair hb₁).comp (fp_bool_gate (fun q => Bool.xor q.1 q.2))
  have hv₂ := (hv₁.pair hb₂).comp (fp_bool_gate (fun q => Bool.xor q.1 q.2))
  exact ((htx.ite hv hx).pair ((hty.ite hv hy).pair hv₂)).congr (fun p => by simp [substitute])

theorem fp_backStep : FP (assignmentCode.prod constraintCode) assignmentCode (fun p => backStep p.1 p.2) := by
  have hx := fp_fst assignmentCode constraintCode
  have he := fp_snd assignmentCode constraintCode
  have hu := he.comp (fp_fst natCode (natCode.prod BitEncoding.bool))
  have hv := (he.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_fst natCode BitEncoding.bool)
  have hb := (he.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_snd natCode BitEncoding.bool)
  have hval := ((hv.pair hx).comp fp_lookup).pair hb |>.comp (fp_bool_gate (fun q => Bool.xor q.1 q.2))
  exact ((hu.pair hval).pair hx).comp (ListMutationMachines.fp_cons (natCode.prod BitEncoding.bool))

theorem fp_forwardStep : FP (forwardCode.prod constraintCode) forwardCode (fun p => forwardStep p.1 p.2) := by
  have hs := fp_fst forwardCode constraintCode
  have hpair := hs.comp (fp_fst (constraintCode.list.prod constraintCode.list) BitEncoding.bool)
  have hxs := hpair.comp (fp_fst constraintCode.list constraintCode.list)
  have hlog := hpair.comp (fp_snd constraintCode.list constraintCode.list)
  have hok := hs.comp (fp_snd (constraintCode.list.prod constraintCode.list) BitEncoding.bool)
  have hh := hxs.comp (ListDecompositionMachines.fp_headD constraintCode (0,0,false))
  have htail := hxs.comp (ListDecompositionMachines.fp_tail constraintCode (0,0,false))
  have hu := hh.comp (fp_fst natCode (natCode.prod BitEncoding.bool))
  have hv := (hh.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_fst natCode BitEncoding.bool)
  have hb := (hh.comp (fp_snd natCode (natCode.prod BitEncoding.bool))).comp (fp_snd natCode BitEncoding.bool)
  have htest := (hu.pair hv).comp NatListSumMachines.fp_equal
  have hnok := (hok.pair hb).comp (fp_bool_gate (fun q => q.1 && !q.2))
  have hself := (htail.pair hlog).pair hnok
  have hsubst := (hh.pair htail).comp
    (ListContextMachines.fp_mapWithContext constraintCode constraintCode constraintCode
      (fun p => substitute p.1.1 p.1.2.1 p.1.2.2 p.2) fp_substitute)
  have hnewlog := (hh.pair hlog).comp (ListMutationMachines.fp_cons constraintCode)
  have hdiff := (hsubst.pair hnewlog).pair hok
  have hnonempty := hxs.comp (ListPredicateMachines.fp_any constraintCode (fun _ => true)
    (fp_const _ BitEncoding.bool true))
  have hne : FP (forwardCode.prod constraintCode) BitEncoding.bool
      (fun p => decide (p.1.1.1 ≠ [])) := hnonempty.congr (fun p => by
    change (p.1.1.1.any (fun _ => true)) = decide (p.1.1.1 ≠ [])
    cases p.1.1.1 <;> rfl)
  exact (hne.ite (htest.ite hself hdiff) hs).congr (fun p => by
    rcases p with ⟨⟨⟨xs,log⟩,ok⟩,e⟩
    cases xs with
    | nil => simp [forwardStep]
    | cons a xs => rcases a with ⟨u,v,b⟩; simp [forwardStep])

end PlanarHom.PlanarityParitySolver
