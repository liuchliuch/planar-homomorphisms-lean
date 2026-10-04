import PlanarHom.TypedBipartiteSpectralCompletion
import PlanarHom.TypedBipartiteSpectralEffectiveAvailability
import PlanarHom.TypedBipartiteSpectralColorTransport

/-!
# Actual typed same-side spectral operations

`TypedBipartiteSpectral.typedRationalPowerAppend_joint` appends every fixed
rational power of the selected positive definite X block, including exponent
zero and negative exponents. `typedEffectiveOverfield_joint` is the fixed-target
effective spectral operation using source3.10's X-entry positivity and product
identities. Both construct ordinary raw TM2 promise reductions, retain every
cross-side companion, use only intrinsic private-X metadata, and return to the
supplied source field basis.

The rational interface uses `Fin q ⊕ Y`; the effective finite-sampling interface
uses `Fin (q+y)`. `domainProblem_color_equiv` identifies these exact raw promise
problems under `finSumFinEquiv`, including all intrinsic domain restrictions.

Only X spectral data occur in rational interpolation. Effective interpolation
repeats existing X entries at unused ambient positions; it does not adjoin a
dummy eigenvalue or require product identities of an ambient completion.
-/
