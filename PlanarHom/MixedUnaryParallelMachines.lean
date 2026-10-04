import PlanarHom.RawGraphTransformMachines
import PlanarHom.MixedProductSemantics
import PlanarHom.ListMapMachines

/-! Actual selected-unary occurrence replication. An internal temporary loop
list reuses the compiled binary replication routine; no temporary graph is ever
submitted to an oracle. The output binary incidence graph is unchanged. -/
namespace PlanarHom.Complexity.MixedCode
open Turing PlanarHom.MachineComposition PlanarHom.MachinePairing
open PairProjectionMachines

private def unaryItemEncoding : BitEncoding (ℕ × ℕ):=BitEncoding.nat.prod BitEncoding.nat
private def edgeItemEncoding : BitEncoding (ℕ × (ℕ × ℕ)):=
  BitEncoding.nat.prod unaryItemEncoding

def unaryAsLoop (u : ℕ × ℕ) : ℕ × (ℕ × ℕ):=(u.1,u)
def unaryLoopGraph (g : MixedCode) : MixedCode:=⟨g.vertices,g.unaries.map unaryAsLoop,[]⟩

theorem fp_vertices : FP encoding BitEncoding.unaryNat vertices:=by
  simpa only [Function.comp_apply] using
    (fp_fst BitEncoding.unaryNat (edgeEncoding.prod unaryEncoding)).transportInput
      (fun g : MixedCode=>(g.vertices,g.edges,g.unaries)) (fun _=>rfl)

private theorem fp_unaryAsLoop : FP unaryItemEncoding edgeItemEncoding unaryAsLoop:=
  (fp_fst BitEncoding.nat BitEncoding.nat).pair (fp_id unaryItemEncoding)

private theorem fp_unaryLoopGraph : FP encoding encoding unaryLoopGraph:=by
  have hloop:=fp_unaries.comp (PlanarHom.ListMapMachines.fp_map unaryItemEncoding edgeItemEncoding
    unaryAsLoop fp_unaryAsLoop)
  exact (fp_vertices.pair (hloop.pair (fp_const encoding unaryEncoding []))).transportOutput (fun _=>rfl)

private theorem lower_replicated (selected s : ℕ) (us : List (ℕ × ℕ)) :
    (repeatSelected (fun e : ℕ × (ℕ × ℕ)=>decide (e.2.2=selected)) s
      (us.map unaryAsLoop)).map Prod.snd =
      repeatSelected (fun u : ℕ × ℕ=>decide (u.2=selected)) s us:=by
  induction us with
  | nil=>rfl
  | cons u us ih=>
    simp only [List.map_cons,repeatSelected_cons,List.map_append,unaryAsLoop]
    by_cases hu:u.2=selected <;> simp [hu,ih]

/-- Actual polynomial-time selected unary thickening under the exact graph code. -/
theorem fp_parallelUnaryLabel (selected : ℕ) :
    FP (BitEncoding.unaryNat.prod encoding) encoding (fun p=>p.2.parallelUnaryLabel selected p.1):=by
  let input:=BitEncoding.unaryNat.prod encoding
  have hs : FP input BitEncoding.unaryNat Prod.fst:=fp_fst _ _
  have hg : FP input encoding Prod.snd:=fp_snd _ _
  have htemp:= (hs.pair (hg.comp fp_unaryLoopGraph)).comp
    (PlanarHom.MixedParallelMachines.fp_parallelLabel selected)
  have hu:=(htemp.comp fp_edges).comp
    (PlanarHom.ListMapMachines.fp_map edgeItemEncoding unaryItemEncoding Prod.snd
      (fp_snd BitEncoding.nat unaryItemEncoding))
  have hall:= (hg.comp fp_vertices).pair ((hg.comp fp_edges).pair hu)
  apply hall.transportOutput
  intro p
  have he:=lower_replicated selected p.1 p.2.unaries
  simp only [BitEncoding.prod,encoding,BitEncoding.retract,parallelUnaryLabel,
    unaryLoopGraph,parallelLabel,Function.comp_apply] at he ⊢
  rw [he]
  rfl

noncomputable def parallelUnaryComputer (selected : ℕ) :
    TM2ComputableInPolyTime (BitEncoding.unaryNat.prod encoding).toFinEncoding encoding.toFinEncoding
      (fun p=>p.2.parallelUnaryLabel selected p.1):=
  Classical.choice (fp_parallelUnaryLabel selected)

/-- Full successful-raw-decoding extension, including noncanonical unary labels. -/
noncomputable def parallelUnaryRawComputer (selected : ℕ) :
    TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding (fun w=>w.value.2.parallelUnaryLabel selected w.value.1):=
  composeComputers (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (parallelUnaryComputer selected)

/-- Exact raw execution guarantee for every successful decoder input. -/
noncomputable def parallel_unary_raw_outputs (selected : ℕ) (raw : Bits) (s : ℕ) (g : MixedCode)
    (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (s,g)) :
    TM2OutputsInTime (parallelUnaryRawComputer selected).tm
      (raw.map (parallelUnaryRawComputer selected).inputAlphabet.symm)
      (some ((encoding.encode (g.parallelUnaryLabel selected s)).map
        (parallelUnaryRawComputer selected).outputAlphabet.symm))
      ((parallelUnaryRawComputer selected).time.eval raw.length):=by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding):=⟨raw,⟨(s,g),hd⟩⟩
  have hv : w.value=(s,g):=BitEncoding.ValidWord.value_eq hd
  have h:=(parallelUnaryRawComputer selected).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,hv,w] using h

end PlanarHom.Complexity.MixedCode
