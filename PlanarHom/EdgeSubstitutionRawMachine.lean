import PlanarHom.EdgeSubstitutionCode

/-! NEW reconstruction of actual raw-word execution for edge substitution.
Normalization charges the real input length, including noncanonical words. -/
noncomputable section
namespace PlanarHom.EdgeSubstitution
open Complexity FixedGadgetNetwork

def substituteComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime MixedCode.encoding.toFinEncoding MixedCode.encoding.toFinEncoding
      (substitute ts) := Classical.choice (fp_substitute ts)

def substituteRawComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding MixedCode.encoding).toFinEncoding MixedCode.encoding.toFinEncoding
      (fun w=>substitute ts w.value) :=
  MachineComposition.composeComputers (g:=substitute ts) MixedCode.normalizer (substituteComputer ts)

/-- Every successfully decoded raw graph has this actual TM2 execution, with
no validity, planarity, target availability, or output-size hypothesis. -/
def substitute_raw_outputs (ts : List Template) (raw : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode raw=some g) :
    Turing.TM2OutputsInTime (substituteRawComputer ts).tm
      (raw.map (substituteRawComputer ts).inputAlphabet.symm)
      (some ((MixedCode.encoding.encode (substitute ts g)).map
        (substituteRawComputer ts).outputAlphabet.symm))
      ((substituteRawComputer ts).time.eval raw.length) := by
  let w : BitEncoding.ValidWord MixedCode.encoding := ⟨raw,⟨g,hd⟩⟩
  have hv : w.value=g := BitEncoding.ValidWord.value_eq hd
  have h := (substituteRawComputer ts).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,w,hv] using h

end PlanarHom.EdgeSubstitution
