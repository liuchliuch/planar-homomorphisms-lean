import PlanarHom.OccurrenceKasteleynPeelingMachines

namespace ReimplementedOrientation
open PlanarHom.MultiGraph.Kasteleyn

 theorem empty_log : computeOrientation [] = [] := rfl
 theorem satisfied_singleton : computeOrientation [(0,[(7,true)])] = [] := by decide
 theorem reversed_singleton : computeOrientation [(0,[(7,false)])] = [7] := by decide
 theorem repeated_even_dart : computeOrientation [(0,[(7,false),(7,false)])] = [] := by decide
 theorem malformed_empty_row : computeOrientation [(0,[])] = [] := by decide
 theorem huge_binary_label : computeOrientation [(123456789,[(987654321,false)])] = [987654321] := by decide
 theorem exact_iterative_agreement (table : List RawFace) :
    computeOrientationIterative table = computeOrientation table :=
  computeOrientationIterative_eq_computeOrientation table

example : PlanarHom.Complexity.FP tableCode logCode computeOrientation := fp_computeOrientation

#eval computeOrientation []
#eval computeOrientation [(0,[(7,true)])]
#eval computeOrientation [(0,[(7,false)])]
#eval computeOrientation [(0,[(7,false),(7,false)])]
#eval computeOrientation [(0,[])]
#eval computeOrientation [(123456789,[(987654321,false)])]
#eval computeOrientation [(0,[(7,false)]),(1,[(8,false)])]
#eval computeOrientation [(0,[(7,false)]),(0,[(8,false)])]

end ReimplementedOrientation
