# Mathematical expansion of the selected theorem

This is a public guide to the ratified main-theorem proof. The selected source
is Theorem 1.1 of *The conformal Poisson embedding method for the anisotropic
Calderón problem with a potential*, arXiv:2610.13592v1. The precise native
definitions and theorem statement are frozen in
[`ComparatorChallenges/ConformalPoisson.lean`](../../ComparatorChallenges/ConformalPoisson.lean).
Declaration names below refer to [`Solution.lean`](../../Solution.lean).

## Geometry and conventions

Write `d = n + 1` for the manifold dimension, with `2 ≤ n`, so `d ≥ 3`.
The two spaces are compact connected Hausdorff real analytic manifolds with
boundary, modeled on a Euclidean half-space. Their metrics and independent
real-valued potentials are analytic up to the boundary. The operator is

\[
L_{g,q}u=-\operatorname{div}_g\nabla_g u+qu.
\]

The potentials have no sign restriction. Nonresonance means the smooth
zero-Dirichlet kernel is trivial. Measurements use actual correct Dirichlet
solvers and the outward unit normal. Integrals use native Riemannian volume;
boundary integrals use the unsigned volume of the induced boundary metric.

An analytic identification of the full boundaries is specified. The observed
patch is an arbitrary nonempty relative-open subset, represented by an
ambient open set `V`. Only smooth boundary data compactly supported in that
patch are measured. The local DN equality is quantified over all such data.

The target is one unique pair `(J,c)` on the interior together with the observed
patch, where `J` is an analytic diffeomorphism and `c` is positive and analytic.
It has the prescribed boundary identification, `c = 1` and outward normal
derivative zero on the observed patch, and satisfies

\[
J^*g_2=c^{4/(d-2)}g_1,\qquad
q_2\circ J=c^{-(d+2)/(d-2)}L_{g_1,q_1}c,
\]

as well as `u₁(f) = c · (u₂(f ∘ β⁻¹) ∘ J)` for every original supported datum.
The map and multiplier precede the datum in the quantifiers. The conclusion
does not prescribe the behavior on the unobserved boundary.

## Native analytical tools

The final theorem constructs the needed consequences of the analytical
interfaces rather than retaining them as independent literature premises.

* The signed nonresonant inhomogeneous Dirichlet inverse is obtained for the
  actual native operator, with smooth readback from the weak solution.
  `forwardInhomogeneous` supplies the corresponding interface.
* Local Schauder estimates and a native normal-trace inverse estimate control
  actual solutions and their outward derivatives. The inverse constant is
  chosen before the forcing and solution to which it is applied.
* The native Green/Poisson construction represents the same Dirichlet solver
  using the actual metric volume and boundary measure; `nativeGreenKernel`
  supplies the required Green-kernel consequence.
* Finite-jet Runge approximation realizes the compatible second-order jets
  needed for local coordinates and coefficient recovery, with the original
  supported data and the same native solvers.
* Interior analytic regularity is proved only for the actual local smooth
  solutions needed here. Localized translations form an analytic operator
  family; inversion and native readback give analytic dependence and hence
  interior analyticity. The smooth spatial cutoff is not assumed analytic.
* Boundary analytic regularity is proved at the observed boundary points where
  the relevant datum is locally analytic. Native analytic normal coordinates,
  normalized local operators, and factorial derivative bounds give the analytic
  half-space readback. This does not require all measured data to be analytic
  on the full boundary.

The standard monograph background includes elliptic regularity, Dirichlet
inversion, and boundary operator methods. Its role is mathematical guidance.
The formal dependencies are the proved project declarations, Mathlib, and
the attributed Tau Ceti modules at the recorded revisions. No recent-paper
theorem is inserted as an unproved premise of the selected root.

## Boundary gauge and determination

At an observed boundary point, solve with a supported boundary datum equal to
one near that point. The solution is positive on a sufficiently small collar.
Use it to construct positive smooth conformal gauges, analytic on the needed
collar, that make the gauged potentials vanish there. The potentials are not
asserted to vanish globally. The common analytic boundary coordinates then
give actual Gaussian normal charts for the gauged metrics.

Write `G` for the tangential Gram matrix, `A = G⁻¹`,
`κ = sqrt(ξᵀAξ)` for nonzero tangential frequency, and
`τ = trace(G ∂ₜA)`. The native coordinate operator has the form

\[
L=-\partial_t^2+\tfrac12\tau\partial_t
  -\sum A^{ab}\partial_a\partial_b-\sum c^a\partial_a
\]

on the collar where the gauged potential is zero. The proof constructs finite
polynomial-times-exponential boundary layers for this second-order operator.
The amplitude is included in the finite transport equations. Taylor cancellation,
cutoff control, and exponential decay give the actual residual estimates.

The two sides use the same original supported real and imaginary boundary
data, transported by the given boundary identification. Applying the native
signed inverse estimate to the approximation minus the actual solver turns
the residual bound into a normal-trace error bound. Normal coordinate
conversion and removal of the common oscillatory phase give finite trace
expansions with equal coefficients, because the original DN measurements agree.

The leading coefficient determines the principal tangential quadratic form.
At each subsequent order, the exact highest-jet response, lower-jet induction,
and the native inverse/Gram identities recover the next actual normal metric
jet. The dimension restriction `2 ≤ n` enters the injective algebraic recovery.
The open tangential patch and collar are fixed before the jet order and
frequency. Thus the result gives all normal jets on one common open face patch.

Analyticity now gives equality of the metric germs on a single smaller
neighborhood. Separately, the protected finite recurrence constructs a smooth
homogeneous raw symbol family for the actual metric field. Metric germ equality
transfers the same component sequence to the other field. This produces the
localized raw-family consequence used by the existing seed construction.
Metric jets have already been proved at this point, so this transfer does not
use symbol equality to establish its own premise.

This is the accepted finite-layer route. It proves the consequence required by
the main theorem, without a general formal theorem identifying the whole DN
pseudodifferential symbol with that raw recurrence.

## Local seed and global continuation

The boundary metric germ gives a local isometry for the gauged metrics.
Boundary Cauchy uniqueness relates every original supported solution through
the same local map and multiplier. Finite-jet Runge approximation supplies
quotient coordinates with a common nonvanishing denominator. These coordinates
identify points and scales and permit analytic continuation of that relation.

The continuation keeps one map and multiplier relating all original data.
The no-escape argument distinguishes observed and unobserved target limits.
For the difficult unobserved case it constructs an analytic continued inverse
from solution quotients and derives a weak-conformal constant-germ
contradiction. Compactness and continuation then give the global interior map.
The reverse construction proves invertibility. Compatible boundary seeds
attach every observed boundary point. Local normalization and continuation
give the two gauge identities and the unique realizing `GaugePair`.

This analytic no-escape route is the second accepted departure from the
manuscript. The separate smooth curvature-blow-up lemma is outside the
selected formalization scope.

## Exact delivered claim

`ConformalPoisson.theorem_1_1` closes this chain under the original geometric
and measurement data. `ConformalPoisson.commonPointAndScale` in
[`Consumer.lean`](../../Consumer.lean) applies it and retains the same pair
for every original datum. Historical conditional intermediate declarations
remain available, but their inputs are supplied by the final theorem.

This document is an explanatory source map. Formal proof evidence comes from
the source, the allowed-axiom audit, the comparator, and kernel replay described
in [verification](../VERIFICATION.md).
