import PlanarHom.FixedGadgetNetworkBounds
import PlanarHom.GraphCodeNormalization

/-! A genuine polynomial-time TM2 for the complete literal network fold, plus
canonicalization of every successfully decoded raw network representation. -/
noncomputable section
namespace PlanarHom.FixedGadgetNetwork
open Complexity

/-- No template, network, planarity, label or port validity is assumed. -/
theorem fp_compile (ts : List Template) : FP networkEncoding MixedCode.encoding (compile ts) := by
  have h := ListFoldMachines.fp_foldl gateEncoding MixedCode.encoding (compileStep ts)
    (fp_compileStep ts)
    (Polynomial.C (20*(familyCost ts+1)^2)*(Polynomial.X+1)^2)
    (fun g as i _=>compile_prefix_size_bound ts g as i)
  exact h.transportInput (fun n : Network=>(n.base,n.gates)) (fun _=>rfl)

def compileComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime networkEncoding.toFinEncoding MixedCode.encoding.toFinEncoding
      (compile ts) := Classical.choice (fp_compile ts)

def networkNormalizer : BitEncoding.Normalizer networkEncoding := by
  apply BitEncoding.retractNormalizer (MixedCode.encoding.prod gateEncoding.list)
    (fun n : Network=>(n.base,n.gates)) (fun p=>⟨p.1,p.2⟩)
    (by intro n; cases n; rfl) (by intro p; cases p; rfl)
  exact BitEncoding.prodNormalizer MixedCode.normalizer
    (BitEncoding.listNormalizer (BitEncoding.prodNormalizer BitEncoding.natNormalizer
      (BitEncoding.listNormalizer BitEncoding.natNormalizer)))

def compileRawComputer (ts : List Template) :
    Turing.TM2ComputableInPolyTime
      (BitEncoding.ValidWord.encoding networkEncoding).toFinEncoding MixedCode.encoding.toFinEncoding
      (fun w=>compile ts w.value) :=
  MachineComposition.composeComputers networkNormalizer (compileComputer ts)

/-- The actual raw input length pays for normalization and all compilation.
The decoded network may be malformed; no semantic promise is needed. -/
def compile_raw_outputs (ts : List Template) (raw : Bits) (n : Network)
    (hd : networkEncoding.decode raw=some n) :
    Turing.TM2OutputsInTime (compileRawComputer ts).tm
      (raw.map (compileRawComputer ts).inputAlphabet.symm)
      (some ((MixedCode.encoding.encode (compile ts n)).map
        (compileRawComputer ts).outputAlphabet.symm))
      ((compileRawComputer ts).time.eval raw.length) := by
  let w : BitEncoding.ValidWord networkEncoding := ⟨raw,⟨n,hd⟩⟩
  have hv : w.value=n := BitEncoding.ValidWord.value_eq hd
  have h := (compileRawComputer ts).outputsFun w
  simpa only [BitEncoding.toFinEncoding,BitEncoding.ValidWord.encoding,
    BitEncoding.ValidWord.raw,w,hv] using h

end PlanarHom.FixedGadgetNetwork
