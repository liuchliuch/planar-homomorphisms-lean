import PlanarHom.NoncrossingBouquetCarrier

/-! NEW exact literal face-cycle decrement under one adjacent paired-occurrence deletion. -/
noncomputable section
namespace PlanarHom.NoncrossingBouquet
open MultiGraph.Kasteleyn FinitePermutationCycles PlanarityLRRealization
variable {E : Type*} [DecidableEq E] [Finite E]

theorem count_delete_adjacent_pair (word : List (Dart E)) (hn : word.Nodup) (hfull : ∀a,a∈word)
    (a : Dart E) (pre post : List (Dart E)) (hw : word=pre++a::(a.1,!a.2)::post)
    (hne : eraseOccurrence a.1 word≠[]) :
    count (word.formPerm * reversePerm E)=
      count ((eraseOccurrence a.1 word).formPerm * reversePerm {e:E // e≠a.1})+1 := by
  let ys:=eraseOccurrence a.1 word
  let rot:=ys.rotate pre.length
  have hny : ys.Nodup:=eraseOccurrence_nodup a.1 word hn
  have hnr : rot.Nodup:=List.nodup_rotate.mpr hny
  have hfr : ∀b,b∈rot := fun b=>List.mem_rotate.mpr (eraseOccurrence_full a.1 word hfull b)
  have hrne : rot≠[] := by
    intro hr
    have hh:=congrArg List.length hr
    simp only [rot,List.length_rotate,List.length_nil] at hh
    exact hne (List.length_eq_zero_iff.mp hh)
  have hmap : rot.map (remainingLift a.1)=post++pre := by
    change (ys.rotate pre.length).map _=_
    rw [List.map_rotate,eraseOccurrence_decomposition word hn a pre post hw,
      List.rotate_eq_drop_append_take (by simp)]
    simp
  have hrot : word.rotate pre.length=a::(a.1,!a.2)::(post++pre) := by
    rw [hw,List.rotate_eq_drop_append_take (by simp)]
    simp
  have htrans:=count_pairWord_transport a rot hnr hfr
  rw [hmap,←hrot,List.formPerm_rotate word hn pre.length] at htrans
  rw [←htrans]
  have hc : count ((pairWord rot).formPerm * pairReverse (reversePerm {e:E // e≠a.1}))=
      count (rot.formPerm * reversePerm {e:E // e≠a.1})+1 := by
    cases hr : rot with
    | nil => exact (hrne hr).elim
    | cons c cs => exact count_pairWord _ c cs (hr ▸ hnr) (fun b=>hr ▸ hfr b)
  rw [hc]
  change count ((ys.rotate pre.length).formPerm * _)+1=count (ys.formPerm * _)+1
  rw [List.formPerm_rotate ys hny pre.length]

end PlanarHom.NoncrossingBouquet
