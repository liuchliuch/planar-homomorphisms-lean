import PlanarHom.MachineCodeTransport
import PlanarHom.PairProjectionMachines

/-! Concrete projections of the project's actual list and graph codewords. -/

namespace PlanarHom.Complexity

open Turing PairProjectionMachines PlanarHom.MachineComposition

namespace ListCodecMachines

/-- Extract the encoded binary list length from the actual framed header. -/
noncomputable def lengthComputer {α : Type} (e : BitEncoding α) :
    TM2ComputableInPolyTime e.list.toFinEncoding BitEncoding.nat.toFinEncoding
      (List.length : List α → ℕ) :=
  transportInputComputer e.list (BitEncoding.nat.prod BitEncoding.bits) BitEncoding.nat
    (fun xs => (xs.length,BitEncoding.frames (xs.map e.encode))) (fun _=>rfl)
    (fstEncodingComputer BitEncoding.nat BitEncoding.bits)

/-- Remove precisely the list-length header, leaving the sequence of fully
materialized framed item words. No parsing or encoding work is treated as free. -/
noncomputable def payloadComputer {α : Type} (e : BitEncoding α) :
    TM2ComputableInPolyTime e.list.toFinEncoding BitEncoding.bits.toFinEncoding
      (fun xs => BitEncoding.frames (xs.map e.encode)) :=
  transportInputComputer e.list (BitEncoding.nat.prod BitEncoding.bits) BitEncoding.bits
    (fun xs => (xs.length,BitEncoding.frames (xs.map e.encode))) (fun _=>rfl)
    (sndEncodingComputer BitEncoding.nat BitEncoding.bits)

theorem fp_length {α : Type} (e : BitEncoding α) :
    FP e.list BitEncoding.nat (List.length : List α → ℕ) := ⟨lengthComputer e⟩

theorem fp_payload {α : Type} (e : BitEncoding α) :
    FP e.list BitEncoding.bits (fun xs => BitEncoding.frames (xs.map e.encode)) := ⟨payloadComputer e⟩

end ListCodecMachines

namespace GraphCode

/-- The exact edge-list codec used by `GraphCode.encoding`. -/
def edgeEncoding : BitEncoding (List (ℕ × ℕ)) := (BitEncoding.nat.prod BitEncoding.nat).list

/-- Extract the unary vertex count from an actual serialized graph code. -/
noncomputable def verticesComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.unaryNat.toFinEncoding vertices :=
  transportInputComputer encoding (BitEncoding.unaryNat.prod edgeEncoding) BitEncoding.unaryNat
    (fun g => (g.vertices,g.edges)) (fun _=>rfl)
    (fstEncodingComputer BitEncoding.unaryNat edgeEncoding)

/-- Extract the complete edge occurrence list without changing multiplicity,
loop occurrences, endpoint values, or their order. -/
noncomputable def edgesComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding edgeEncoding.toFinEncoding edges :=
  transportInputComputer encoding (BitEncoding.unaryNat.prod edgeEncoding) edgeEncoding
    (fun g => (g.vertices,g.edges)) (fun _=>rfl)
    (sndEncodingComputer BitEncoding.unaryNat edgeEncoding)

/-- Count edge occurrences by the actual encoded length header; this has no
endpoint-validity or planarity assumption and retains parallel-edge multiplicity. -/
noncomputable def edgeCountComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding BitEncoding.nat.toFinEncoding
      (fun g => g.edges.length) :=
  composeComputers edgesComputer (ListCodecMachines.lengthComputer (BitEncoding.nat.prod BitEncoding.nat))

theorem fp_vertices : FP encoding BitEncoding.unaryNat vertices := ⟨verticesComputer⟩
theorem fp_edges : FP encoding edgeEncoding edges := ⟨edgesComputer⟩
theorem fp_edgeCount : FP encoding BitEncoding.nat (fun g=>g.edges.length) := ⟨edgeCountComputer⟩

end GraphCode

namespace MixedCode

def edgeEncoding : BitEncoding (List (ℕ × (ℕ × ℕ))) :=
  (BitEncoding.nat.prod (BitEncoding.nat.prod BitEncoding.nat)).list

def unaryEncoding : BitEncoding (List (ℕ × ℕ)) := (BitEncoding.nat.prod BitEncoding.nat).list

/-- Typed mixed-code components are extracted by concrete framed projections. -/
noncomputable def occurrencesComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding
      (edgeEncoding.prod unaryEncoding).toFinEncoding (fun g => (g.edges,g.unaries)) :=
  transportInputComputer encoding
    (BitEncoding.unaryNat.prod (edgeEncoding.prod unaryEncoding))
    (edgeEncoding.prod unaryEncoding) (fun g => (g.vertices,(g.edges,g.unaries))) (fun _=>rfl)
    (sndEncodingComputer BitEncoding.unaryNat (edgeEncoding.prod unaryEncoding))

noncomputable def edgesComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding edgeEncoding.toFinEncoding edges :=
  composeComputers (f := fun g : MixedCode => (g.edges,g.unaries)) (g := Prod.fst)
    occurrencesComputer (fstEncodingComputer edgeEncoding unaryEncoding)

noncomputable def unariesComputer :
    TM2ComputableInPolyTime encoding.toFinEncoding unaryEncoding.toFinEncoding unaries :=
  composeComputers (f := fun g : MixedCode => (g.edges,g.unaries)) (g := Prod.snd)
    occurrencesComputer (sndEncodingComputer edgeEncoding unaryEncoding)

theorem fp_edges : FP encoding edgeEncoding edges := ⟨edgesComputer⟩
theorem fp_unaries : FP encoding unaryEncoding unaries := ⟨unariesComputer⟩

end MixedCode

end PlanarHom.Complexity
