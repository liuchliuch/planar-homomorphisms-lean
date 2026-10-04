import PlanarHom.TypedGadgetAppendCompiler
import PlanarHom.GraphCodeNormalization

/-! The literal typed-template query compiler is a real Turing machine on
arbitrary decodable raw words, with its compiled polynomial time bound. -/
noncomputable section
namespace PlanarHom.TypedGadgetAppend
open Complexity FixedGadgetNetwork EdgeSubstitution

def queryComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime MixedCode.encoding.toFinEncoding MixedCode.encoding.toFinEncoding
      (substitute ts) := Classical.choice (fp_substitute ts)

def queryRawComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding MixedCode.encoding).toFinEncoding MixedCode.encoding.toFinEncoding
      (fun w=>substitute ts w.value) :=
  MachineComposition.composeComputers (f:=BitEncoding.ValidWord.value) (g:=substitute ts)
    MixedCode.normalizer (queryComputer ts)

def query_raw_outputs (ts : List Template) (raw : Bits) (g : MixedCode)
    (hd : MixedCode.encoding.decode raw=some g) :
    Turing.TM2OutputsInTime (queryRawComputer ts).tm
      (raw.map (queryRawComputer ts).inputAlphabet.symm)
      (some ((MixedCode.encoding.encode (substitute ts g)).map
        (queryRawComputer ts).outputAlphabet.symm))
      ((queryRawComputer ts).time.eval raw.length) := by
  let w : BitEncoding.ValidWord MixedCode.encoding := ⟨raw,⟨g,hd⟩⟩
  have hv : w.value=g := BitEncoding.ValidWord.value_eq hd
  have h := (queryRawComputer ts).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,w,hv] using h

end PlanarHom.TypedGadgetAppend
