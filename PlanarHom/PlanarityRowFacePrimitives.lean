import PlanarHom.PlanarityRowFaceCodeProgram

/-! NEW unconditional row-table lookup machines and actual retained-payload
bounds for every raw face step, including invalid input rows. -/
namespace PlanarHom.PlanarityRowFaceCode
open Complexity PairProjectionMachines PlanarityRotationCode

 theorem fp_rotation : FP (inputCode.prod dartCode) dartCode (fun p=>rotation p.1.1 p.1.2 p.2) := by
  have hc:=fp_fst inputCode dartCode
  have ha:=fp_snd inputCode dartCode
  have hg:=hc.comp (fp_fst MixedCode.encoding rowsCode)
  have hrs:=hc.comp (fp_snd MixedCode.encoding rowsCode)
  have hv:=(hg.pair ha).comp fp_host
  have hr:=(hrs.pair hv).comp (FisherCodeMachines.fp_getD dartCode.list [])
  exact (hr.pair ha).comp PlanarityLRDirect.fp_rowNext

 theorem fp_faceStep : FP (inputCode.prod dartCode) dartCode (fun p=>faceStep p.1.1 p.1.2 p.2) :=
  ((fp_fst inputCode dartCode).pair ((fp_snd inputCode dartCode).comp fp_reverse)).comp fp_rotation

 theorem member_encoding_le {A : Type} (e : BitEncoding A) (xs : List A) (a : A) (ha : a∈xs) :
    (e.encode a).length≤(e.list.encode xs).length := by
  have hh:=ListMapMachines.mem_le_sum_map (fun a=>(e.encode a).length) ha
  dsimp only at hh
  have he:(e.list.encode xs).length=2*(BitEncoding.nat.encode xs.length).length+1+
      2*(xs.map (fun a=>(e.encode a).length)).sum+xs.length := by
    simp [BitEncoding.list,BitEncoding.frames_length,List.map_map,Function.comp_def]
    omega
  omega

 theorem row_member_encoding_le (rows : Rows) (i : ℕ) (a : Dart) (ha : a∈rows.getD i []) :
    (dartCode.encode a).length≤(rowsCode.encode rows).length := by
  rw [List.getD_eq_getElem?_getD] at ha
  cases h:rows[i]? with
  | none => simp [h] at ha
  | some xs =>
    simp only [h,Option.getD_some] at ha
    exact (member_encoding_le dartCode xs a ha).trans
      (member_encoding_le dartCode.list rows xs (List.mem_of_getElem? h))

 theorem reverse_encoding_length (a : Dart) : (dartCode.encode (reverse a)).length=(dartCode.encode a).length := by
  simp [dartCode,reverse,BitEncoding.prod_length,BitEncoding.bool]

 theorem faceStep_word_bound (g : MixedCode) (rows : Rows) (a : Dart) :
    (dartCode.encode (faceStep g rows a)).length≤max (rowsCode.encode rows).length (dartCode.encode a).length := by
  unfold faceStep rotation PlanarityLRDirect.rowNext
  rw [List.getD_eq_getElem?_getD]
  generalize hn:(rows.getD (host g (reverse a)) []).idxOf (reverse a)+1=k
  cases h:(rows.getD (host g (reverse a)) [])[k%(rows.getD (host g (reverse a)) []).length]? with
  | none => simpa only [Option.getD_none,reverse_encoding_length] using Nat.le_max_right (rowsCode.encode rows).length (dartCode.encode a).length
  | some b =>
    exact (row_member_encoding_le rows _ b (List.mem_of_getElem? h)).trans (Nat.le_max_left _ _)

 theorem iterate_word_bound (g : MixedCode) (rows : Rows) (a : Dart) (n : ℕ) :
    (dartCode.encode ((faceStep g rows)^[n] a)).length≤max (rowsCode.encode rows).length (dartCode.encode a).length := by
  induction n with
  | zero => exact Nat.le_max_right _ _
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact (faceStep_word_bound g rows _).trans (max_le (Nat.le_max_left _ _) ih)

end PlanarHom.PlanarityRowFaceCode
