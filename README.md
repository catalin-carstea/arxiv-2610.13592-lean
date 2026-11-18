# Conformal Poisson embedding in Lean

A Lean formalization of Theorem 1.1 of *The conformal Poisson embedding method
for the anisotropic Calderón problem with a potential*, by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad
([selected manuscript, arXiv:2610.13592v1](https://arxiv.org/abs/2610.13592v1)).

The theorem concerns compact connected real analytic Riemannian manifolds with
boundary, of dimension at least three, with independent signed real analytic
potentials and nonresonant Dirichlet problems. Equality of the local
Dirichlet-to-Neumann maps on an arbitrary nonempty open boundary patch determines
a unique analytic diffeomorphism and positive conformal multiplier on the
interior together with that patch. The conclusion includes the metric and
potential gauge identities, both boundary normalizations, and the relation
between all original Dirichlet solutions using the same map and multiplier.

The entry point is `ConformalPoisson.theorem_1_1` in
[`Solution.lean`](Solution.lean). Its explicit arguments are:

```lean
theorem theorem_1_1
    (hn : 2 ≤ n)
    (hconnected₁ : IsConnected (univ : Set M₁))
    (hconnected₂ : IsConnected (univ : Set M₂))
    (A₁ : AnalyticProblem (n := n) (M := M₁))
    (A₂ : AnalyticProblem (n := n) (M := M₂))
    (V₁ : TopologicalSpace.Opens M₁) (V₂ : TopologicalSpace.Opens M₂)
    (D : MatchingMeasurements A₁ A₂ V₁ V₂) :
    TheoremOneOneResult A₁ A₂ V₁ V₂ D
```

Here `n` is the **boundary dimension**; the manifold dimension is `n + 1`.
The surrounding declarations supply the analytic manifold, compactness,
Hausdorff, and Borel instances. `AnalyticProblem` records the actual metric,
potential, and nonresonance. `MatchingMeasurements` records the actual native
solvers, outward unit normals, analytic boundary identification, and local
measurement equality. There is no additional analytical literature-result
hypothesis in this theorem. The exact definitions and full statement are in the
[frozen challenge](ComparatorChallenges/ConformalPoisson.lean).

## Time and system requirements

The project pins Lean **4.36.0-rc2** and Mathlib commit
`2ddf59c8f14245864e6c0ed227a2dab76b9efea2`. The lockfile pins all transitive
dependencies. The required Tau Ceti sources are bundled in this repository.

Use Linux for the sandboxed comparator, with `bubblewrap` (`bwrap`) installed
and usable. Python 3 runs the source-integrity scripts. Allow several
gigabytes of disk space for dependencies and build
outputs. The large `Solution.lean` needs roughly 9.5 GiB of RAM during
elaboration; a machine with at least 16 GiB RAM and other large applications
closed is appropriate. The package requests one Lean worker and a 9728 MiB
Lean allocation limit. A first build and comparator run can take hours;
subsequent builds reuse Lake's incremental cache.

## Build and inspect the sources

Install [elan](https://github.com/leanprover/elan), then run these commands from
this directory. The toolchain is selected by `lean-toolchain`.

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
```

[`Check.lean`](Check.lean) displays the main theorem and the downstream
`ConformalPoisson.commonPointAndScale` theorem, together with their axioms.
The allowed axioms are `propext`, `Quot.sound`, and `Classical.choice`.

## Checking against the challenge

```sh
bash check-challenge.sh
LEAN_NUM_THREADS=1 lake comparator --config ComparatorChallenges/ConformalPoisson.json
```

This uses the comparator shipped with the pinned Lake, with the same JSON
configuration format as
[`anisotropic-calderon-lean`](https://github.com/catalin-carstea/anisotropic-calderon-lean/tree/0f09786282d0f2d3865fa0f175b63c35969d25f7).
It builds and exports the challenge and solution in its sandbox, compares the
selected theorem and the definitions on which its statement depends, audits
the permitted axioms, and replays the solution through Lean's kernel.
`definition_names` is empty: there are no authorized definition holes.
No modified Lake binary, comparator patch, or sandbox bypass is required.

The challenge is a byte-for-byte copy of the ratified frozen reference, with
its single explicit `sorry`. It is compiled separately; the proof imports no
challenge. `check-challenge.sh` checks its pinned digest and the toolchain.
It uses the local frozen reference digest because this paper's challenge was
commissioned in the formalization workspace, rather than in a separate public
challenge repository.

To check the identity of all released proof files and bundled upstream sources:

```sh
python3 scripts/check-sources.py
```

See [verification and release provenance](docs/VERIFICATION.md) for the scope
of the checks and the distinction between the released proof and this package.

## Reading the sources

Start with the [proof guide](docs/PROOF_GUIDE.md) and
[mathematical expansion](docs/expansion/README.md).

| Path | Contents |
|---|---|
| [`Solution.lean`](Solution.lean) | Native definitions, assembled proof, and final theorem |
| [`Consumer.lean`](Consumer.lean) | Uses one recovered map and multiplier for every original boundary datum |
| [`Proof/`](Proof/) | 815 released support modules, including attributed Mathlib and Tau Ceti supplements |
| [`TauCeti/`](TauCeti/) | 253 unchanged upstream modules needed by the imports |
| [`ComparatorChallenges/`](ComparatorChallenges/) | Frozen theorem challenge and Lake comparator configuration |
| [`docs/release/`](docs/release/) | Source digests and public release provenance |

The mathematical proof sources are preserved byte-for-byte from the ratified
release, including the assembled module name `Solution`. Historical conditional
theorems and development comments remain in that source. The final theorem
supplies their analytical inputs with proved producers; names or comments about
earlier stages do not describe additional premises of the final theorem.

## Scope

This is a formalization of the main theorem. The analytical consequences needed
by that theorem are proved in the project from the pinned libraries. General
versions of every cited PDE theorem are not separate claims of this package.
Standard monographs guide the analytical arguments; their results are not
introduced as extra axioms or unproved theorem parameters.

Two accepted proof-route departures are recorded in the proof guide. Boundary
determination uses finite second-order boundary layers to recover metric jets,
followed by analytic germ equality and transfer of a common raw symbol family.
Global no-escape uses analytic continuation of an inverse and a weak-conformal
constant-germ contradiction. This package does not claim a formalization of the
manuscript's separate smooth curvature-blow-up lemma or a general identification
of the complete Dirichlet-to-Neumann pseudodifferential symbol.

## License and citation

The project's original contributions are under the
[BSD 3-Clause License](LICENSE). Bundled third-party code retains its original
copyright and license; see [third-party notices](THIRD_PARTY_NOTICES.md).
[`CITATION.cff`](CITATION.cff) supplies the four authors' citation metadata.

## Acknowledgements

This formalization was developed with AI-assisted proof authoring and independent
AI reader sessions, followed by human ratification. Lean, Mathlib, Tau Ceti,
and the earlier anisotropic Calderón formalization supply substantial library
and proof support. Their authorship is credited separately in the third-party
notices. The package layout and comparator workflow follow the reference
repository linked above.
