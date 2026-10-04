import PlanarHom.RootedCodeSemantics

/-! Actual raw-word extension of the rooted query compiler, including alternate
natural root words and alternate graph headers/endpoints. -/
noncomputable section
namespace PlanarHom.RootedCodeMachines
open Complexity Turing MachineComposition
variable {n m : ℕ}

def computer (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) :
    TM2ComputableInPolyTime inputEncoding.toFinEncoding MixedCode.encoding.toFinEncoding
      (attach H selected) := Classical.choice (fp_attach H selected)

def rawComputer (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) :
    TM2ComputableInPolyTime (BitEncoding.ValidWord.encoding inputEncoding).toFinEncoding
      MixedCode.encoding.toFinEncoding (fun w => attach H selected w.value) :=
  composeComputers (BitEncoding.prodNormalizer BitEncoding.natNormalizer MixedCode.normalizer)
    (computer H selected)

def raw_outputs (H : RootedGraph (Fin n) (Fin m)) (selected : ℕ) (raw : Bits)
    (r : ℕ) (g : MixedCode) (hd : inputEncoding.decode raw=some (r,g)) :
    TM2OutputsInTime (rawComputer H selected).tm
      (raw.map (rawComputer H selected).inputAlphabet.symm)
      (some ((MixedCode.encoding.encode (attach H selected (r,g))).map
        (rawComputer H selected).outputAlphabet.symm))
      ((rawComputer H selected).time.eval raw.length) := by
  let w : BitEncoding.ValidWord inputEncoding := ⟨raw,⟨(r,g),hd⟩⟩
  have hv : w.value=(r,g) := BitEncoding.ValidWord.value_eq hd
  have h := (rawComputer H selected).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,hv,w] using h

end PlanarHom.RootedCodeMachines
