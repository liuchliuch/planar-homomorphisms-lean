import PlanarHom.PlanarityLRDualReachability
import PlanarHom.RadialPottsAssemblyCircleArches
import PlanarHom.PlanarityLRFaceAxiomAudit

namespace PlanarHom.PlanarityLRRealization.Regression
open Set
example : Disjoint (Set.range (arch 0 0 4)) (Set.range (arch 0 1 3)) := by
  apply arch_ranges_disjoint_unordered <;> norm_num [Noninterleaving]
example : Disjoint (Set.range (arch 0 4 0)) (Set.range (arch 0 3 1)) := by
  apply arch_ranges_disjoint_unordered <;> norm_num [Noninterleaving]
example : Disjoint (Set.range (arch 7 0 1)) (Set.range (arch 7 2 3)) := by
  apply arch_ranges_disjoint_unordered <;> norm_num [Noninterleaving]
example : Function.Injective (arch 0 7 (-2)) := arch_injective_of_ne _ _ _ (by norm_num)
end PlanarHom.PlanarityLRRealization.Regression
