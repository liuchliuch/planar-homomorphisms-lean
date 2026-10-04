import PlanarHom
import Lean.Util.CollectAxioms

/-! Recheck that the five completed source statements do not depend on the mixed
input semantics whose prescribed-domain encoding is still being extended. -/
open Lean Elab Command
run_cmd do
  let env ← getEnv
  let targets := #[`PlanarHom.tensorPower_linearIndependent,
    `PlanarHom.hadamard_weighted_gram_posDef, `PlanarHom.lemma_3_9,
    `PlanarHom.KernelContinuation.posDef_distanceKernel,
    `PlanarHom.CartesianGeometry.cartesian_product_characterization,
    `PlanarHom.FixedChartClosedness.isClosed_nonnegativeClass_support,
    `PlanarHom.FixedChartClosedness.nonnegativeClass_of_tendsto_fixedSupport]
  for target in targets do
    unless env.contains target do throwError m!"Missing completed theorem {target}"
    let (_, s) := ((Lean.CollectAxioms.collect target).run env).run {}
    for (name, _) in env.constants.toList do
      if (`PlanarHom.Complexity).isPrefixOf name && s.visited.contains name then
        throwError m!"Completed theorem {target} depends on computation semantics {name}"
    logInfo m!"SCOPE_PASS {target}: no project Complexity dependency"
