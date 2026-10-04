import PlanarHom.FixedGadgetNetworkCompiler
import PlanarHom.TypedGadgetAppendTyping

/-! New kernel-checked literal-code regressions; the imported typing consumer is
preserved byte for byte from its surviving original source. -/
namespace PlanarHom.FixedGadgetNetwork.Regressions
open Complexity

-- Empty families and empty hosts preserve all original vertices, even isolates.
example : compile [] ⟨⟨3,[],[(2,4)]⟩,[]⟩=⟨3,[],[(2,4)]⟩ := rfl
example (ts : List Template) : compile ts ⟨⟨0,[],[]⟩,[]⟩=⟨0,[],[]⟩ := rfl

-- Out-of-range gate labels select the literal empty template, without erasing
-- old malformed occurrences or arbitrary old unary labels.
example : compile [] ⟨⟨2,[(17,29,31)],[(8,53)]⟩,[(91,[7,11])]⟩=
    ⟨2,[(17,29,31)],[(8,53)]⟩ := by decide

private def pathTemplate : Template := ⟨2,1,[(0,2,0),(2,1,0)],[(2,7)]⟩

-- Repeated endpoints and duplicate gate values remain distinct occurrences,
-- with disjoint fresh blocks and exactly one new intrinsic unary per block.
example : compile [pathTemplate]
    ⟨⟨3,[(0,0,2)],[(0,1),(2,6)]⟩,[(0,[1,1]),(0,[1,1])]⟩=
    ⟨5,[(0,0,2),(1,3,0),(3,1,0),(1,4,0),(4,1,0)],
      [(0,1),(2,6),(3,7),(4,7)]⟩ := by decide

-- Malformed missing ports use the specified zero default. Compilation is total;
-- no proof of validity is smuggled into machine construction.
example : compile [pathTemplate] ⟨⟨0,[],[]⟩,[(0,[])]⟩=
    ⟨1,[(0,0,0),(0,0,0)],[(0,7)]⟩ := by decide

-- Excessive raw ports and very large binary endpoint labels stay literal.
example : compile [pathTemplate] ⟨⟨1,[],[]⟩,[(0,[1099511627776,17,999])]⟩=
    ⟨2,[(1099511627776,1,0),(1,17,0)],[(1,7)]⟩ := by decide

-- Framing failures are rejected by the literal decoder.
example : networkEncoding.decode []=none := by decide

-- Unary vertex words accept noncanonical data bits. This raw word denotes one
-- isolated vertex even though it differs from that network's canonical word.
private def noncanonicalWord : Bits :=
  BitEncoding.frame (BitEncoding.frame [false] ++
    (BitEncoding.frame (edgeItemEncoding.list.encode []) ++ unaryItemEncoding.list.encode [])) ++
      gateEncoding.list.encode []

example : networkEncoding.decode noncanonicalWord=some ⟨⟨1,[],[]⟩,[]⟩ := by
  simp [networkEncoding,noncanonicalWord,MixedCode.encoding,BitEncoding.retract,
    edgeItemEncoding,unaryItemEncoding,BitEncoding.prod,BitEncoding.unaryNat,BitEncoding.decode_encode]
example : noncanonicalWord≠networkEncoding.encode ⟨⟨1,[],[]⟩,[]⟩ := by decide

noncomputable def noncanonicalExecution (ts : List Template) :=
  compile_raw_outputs ts noncanonicalWord ⟨⟨1,[],[]⟩,[]⟩ (by
    simp [networkEncoding,noncanonicalWord,MixedCode.encoding,BitEncoding.retract,
      edgeItemEncoding,unaryItemEncoding,BitEncoding.prod,BitEncoding.unaryNat,BitEncoding.decode_encode])

example (ts : List Template) : FP networkEncoding MixedCode.encoding (compile ts) := fp_compile ts

noncomputable def arbitraryRawOutput (ts : List Template) (raw : Bits) (n : Network)
    (hd : networkEncoding.decode raw=some n) := compile_raw_outputs ts raw n hd

end PlanarHom.FixedGadgetNetwork.Regressions
