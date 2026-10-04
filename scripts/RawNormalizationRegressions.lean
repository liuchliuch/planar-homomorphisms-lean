import PlanarHom.RawGraphTransformMachines

open PlanarHom.Complexity Turing

def rawEdge : Bits:=BitEncoding.frame []++BitEncoding.frame [true]++[false]
def rawMixed : Bits:=BitEncoding.frame [false,false]++
  BitEncoding.frame (BitEncoding.frame [true]++BitEncoding.frame rawEdge)++
  BitEncoding.frame []
def decodedMixed : MixedCode:=⟨2,[(0,(1,2))],[]⟩

theorem rawMixed_decode : MixedCode.encoding.decode rawMixed=some decodedMixed:=by rfl

-- This instantiates the actual ordinary normalization machine on noncanonical
-- unary vertices and a noncanonical binary label, not only the codec equation.
noncomputable def rawMixed_normalization :=
  MixedCode.normalization_outputs rawMixed decodedMixed rawMixed_decode

-- The exact ordinary compiler now emits three selected occurrences, resolving
-- the previous direct caller's raw-byte classifier distinction.
noncomputable def rawMixed_thickening :=
  MixedCode.parallel_raw_outputs 2 (BitEncoding.frame [false,false,false]++rawMixed) 3 decodedMixed (by rfl)

#guard (decodedMixed.parallelLabel 2 3).edges.length == 3
#guard MixedCode.encoding.decode [true] |>.isNone
#guard BitEncoding.nat.list.decode (BitEncoding.frame [false]++BitEncoding.frame []) |>.isNone
#guard BitEncoding.nat.decode [false]==some 2

-- Successful decoding does not imply endpoint validity. Normalization preserves
-- the typed invalid graph too; promise membership must still check its ranges.
def invalidGraph : GraphCode:=⟨1,[(2,0)]⟩
noncomputable def invalidGraph_normalization :=
  GraphCode.normalization_outputs (GraphCode.encoding.encode invalidGraph) invalidGraph
    (GraphCode.encoding.decode_encode invalidGraph)

#print axioms rawMixed_normalization
#print axioms rawMixed_thickening
#print axioms invalidGraph_normalization
