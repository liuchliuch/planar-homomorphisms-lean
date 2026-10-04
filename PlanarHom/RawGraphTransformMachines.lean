import PlanarHom.GraphCodeNormalization
import PlanarHom.MixedParallelMachines

/-! Raw-decoder lifting for the concrete thickening compiler. The same machines
now cover all successfully decoded input words, after proved normalization. -/
namespace PlanarHom.Complexity.MixedCode
open Turing PlanarHom.MachineComposition

noncomputable def parallelRawComputer (selected : ℕ) :
    TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding (BitEncoding.unaryNat.prod encoding)).toFinEncoding
      encoding.toFinEncoding
      (fun w=>w.value.2.parallelLabel selected w.value.1):=
  composeComputers (BitEncoding.prodNormalizer BitEncoding.unaryNormalizer normalizer)
    (PlanarHom.MixedParallelMachines.parallelComputer selected)

/-- Noncanonical count headers, endpoint words, and label words are normalized
before selected-label classification. This repairs the direct raw-byte mismatch. -/
noncomputable def parallel_raw_outputs (selected : ℕ) (raw : Bits) (s : ℕ) (g : MixedCode)
    (hd : (BitEncoding.unaryNat.prod encoding).decode raw=some (s,g)) :
    TM2OutputsInTime (parallelRawComputer selected).tm
      (raw.map (parallelRawComputer selected).inputAlphabet.symm)
      (some ((encoding.encode (g.parallelLabel selected s)).map (parallelRawComputer selected).outputAlphabet.symm))
      ((parallelRawComputer selected).time.eval raw.length):=by
  let w : BitEncoding.ValidWord (BitEncoding.unaryNat.prod encoding):=⟨raw,⟨(s,g),hd⟩⟩
  have hv : w.value=(s,g):=BitEncoding.ValidWord.value_eq hd
  have h:=(parallelRawComputer selected).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,hv,w] using h

end PlanarHom.Complexity.MixedCode
