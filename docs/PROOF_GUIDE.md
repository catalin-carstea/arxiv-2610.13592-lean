# Guide to the proof sources

The final declaration is `ConformalPoisson.theorem_1_1`, near the end of
[`Solution.lean`](../Solution.lean). It calls
`ConformalPoisson.theorem_1_1_dn_symbol_proved`, which supplies the last
boundary-determination input to the earlier analytical and global assembly.

The theorem's native objects and its conclusion occur near the beginning of
the same file. Read these before the implementation of the analytical inputs.

| Subject | Declaration or source marker in `Solution.lean` |
|---|---|
| Native metric, operator, supported boundary data | `Metric`, `schrodinger`, `BoundaryDatum` |
| Actual full-boundary Dirichlet solver | `DirichletSolver` |
| Original analytic problems and measurement data | `AnalyticProblem`, `MatchingMeasurements` |
| Shared geometric conclusion and uniqueness | `GaugePair.RealizesTheorem`, `TheoremOneOneResult` |
| Boundary gauge and common normal charts | `BoundaryGaugePair`, `CommonNormalCharts` |
| Interior analytic quotient coordinates | `exists_interior_analytic_quotient_coordinates_fixed_denominator` |
| Analytic metric germ from boundary jets | source marker `NormalAnalyticGerm.lean` |
| Analytic no-escape argument | `native_noEscape_configuration_impossible` |
| Global assembly | `theorem_1_1_with_analytic_runge` |
| Finite-jet Runge approximation | `analytic_finite_jet_runge` |
| Native signed inhomogeneous Dirichlet inverse | `forwardInhomogeneous` |
| Local Schauder estimate | `localSchauderDirichlet` |
| Native normal-trace estimate | source marker `NativeNormalTraceInverseProved.lean` |
| Native Green and Poisson construction | `nativeGreenKernel` |
| Interior analytic regularity | `nativeInteriorAnalyticRegularity` |
| Boundary analytic regularity | `nativeBoundaryPointAnalyticRegularity`, `nativeBoundaryAnalyticRegularity` |
| Actual finite paired boundary layers | `LocalDN.exists_actual_paired_boundary_layers` |
| Highest-jet response of the trace | `LocalDN.native_trace_highest_jet_response` |
| Metric jets from the original DN data | `LocalDN.nativeMetricJetInput_proved` |
| Common raw symbol family from metric germ | `LocalDN.localizedDN_of_direct_metric_jets` |
| Final theorem | `theorem_1_1_dn_symbol_proved`, `theorem_1_1` |

Search for declaration names in the editor. The assembled source retains
section markers naming its original mathematical components and recording
their provenance. The [component source map](release/SOURCE_MAP.json) lists
the original component names and their line numbers in the assembled file.
The support files under [`Proof/`](../Proof/) provide the
additional imported library results; [`TauCeti/`](../TauCeti/) contains the
required unchanged upstream modules. Imports describe formal dependencies.

## The final analytical caller

The final chain discharges the successive conditional interfaces in this order:

1. `theorem_1_1_dn_symbol_proved` provides the localized DN consequence using
   `LocalDN.localizedDN_of_direct_metric_jets LocalDN.nativeMetricJetInput_proved`.
2. `theorem_1_1_one_input` supplies the proved boundary analytic regularity.
3. `theorem_1_1_three_inputs` supplies the proved interior analytic regularity.
4. `theorem_1_1_five_inputs` supplies the native Green/Poisson and normal-trace
   constructions through the earlier callers.
5. `theorem_1_1_nine_inputs` supplies the native inhomogeneous inverse and
   local Schauder estimate, reaching `theorem_1_1_with_analytic_runge`.

The intermediate interfaces with names ending in `Assumption` are ordinary
Lean propositions. The final caller supplies their proofs. They are not
additional hypotheses of `ConformalPoisson.theorem_1_1`.

[`Consumer.lean`](../Consumer.lean) extracts one realizing `GaugePair` from
the final theorem. It then proves the solution relation for every original
supported boundary datum using that same pair. This checks the intended order
of the existential and universal quantifiers.

## Proof fidelity

The selected scope is the main theorem, with the original analytic geometry,
signed potentials, arbitrary observed patch, actual native solvers, outward
normals, metric volume, and induced unsigned boundary measure. There is no
whole-boundary, positive-potential, Euclidean-ball, or closed-manifold
specialization.

Two proof-route departures were accepted in the ratified release:

* **Boundary determination.** Finite second-order boundary layers recover the
  actual metric jets directly from the local measurements. Analyticity gives
  equality of metric germs, from which one raw symbol family is transferred
  to both sides. The argument does not identify every finite trace coefficient
  with the corresponding coefficient of a general pseudodifferential DN
  symbol. Such a general identification is unnecessary for the selected main
  theorem.
* **No escape.** The global continuation uses an analytic continued inverse
  and a weak-conformal constant-germ contradiction. It does not reproduce
  the manuscript's separate smooth curvature-blow-up argument. The latter
  smooth lemma is not a separately certified theorem of this package.

The [mathematical expansion](expansion/README.md) describes these routes and
the native analytical consequences supplied to the proof.

## Challenge and compilation

[`ComparatorChallenges/ConformalPoisson.lean`](../ComparatorChallenges/ConformalPoisson.lean)
is the unchanged frozen reference, with exactly one selected theorem hole.
Nothing in the proof imports it. The ordinary Lake comparator checks the
statement against the actual theorem in `Solution` and checks the permitted
axioms and kernel acceptance. See [verification](VERIFICATION.md).

The release preserves the assembled declaring module `Solution`. Rearranging
these declarations can change generated auxiliary names in compiled terms.
This package therefore supplies a source map and documentation without
reorganizing the ratified mathematical files.

[`Proof/ProofInfo.lean`](../Proof/ProofInfo.lean) defines the
`without_proof_info in` command used by the large assembled source. It suppresses
editor information during the enclosed theorem elaboration, then restores
the previous information state. It retains ordinary elaboration, diagnostics,
proof terms, and kernel checks. Its purpose is to keep the elaborator's memory
usage within the documented budget.

Historical comments such as “open”, “intake”, or a conditional input count
describe earlier stages retained in the assembled source. The final closed
callers and the compiler's axiom report determine the delivered theorem.
