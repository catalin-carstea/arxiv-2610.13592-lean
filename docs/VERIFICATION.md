# Verification and release provenance

## Exact released proof

The mathematical sources in this package are the ratified release dated
2026-11-18: `Solution.lean`, `Consumer.lean`, and 815 files under `Proof/`.
All 817 files retain their exact released bytes. The challenge is the exact
frozen `Reference.lean`, placed at the public comparator path without editing
its contents. The package adds build configuration, bundled dependency sources,
documentation, citation and license files, and source-integrity scripts.

The underlying frozen contract is
`46606b6f3729146030e29f0be365c8acba77bfd16aa711e4002cf9cfead4bb9c`.
Its successful authoritative check is
`c88c5faf9a6be66d236ab8d17c138a3e4c9ef890556dbff18ba4a755113453b6`.
The project completed three independent semantic readings, one final independent
proof reading tied to those checked source bytes, and human ratification.
Reader independence used separate sessions and procedural access separation
on a shared filesystem; it was not a separately enforced filesystem boundary.

That check freshly compiled all 815 support modules, the actual main proof,
and the frozen consumer. It checked all 113 protected definitions, selected
types and universe parameters, the consumer's actual use of the main theorem,
allowed axioms, foundational primitives, and fresh empty-environment kernel
replay. The frozen definition values were compared exactly. Selected types
were compared with only bound variable labels erased. These are properties
of the original authoritative check, whose mathematical sources this package
preserves; they are not additional claims about Lake's stock comparator.

Compact public provenance is recorded in
[`release/PROVENANCE.json`](release/PROVENANCE.json). Private workflow state,
reader reports, model logs, credentials, and host-specific build configuration
are not part of this source distribution.

## Public comparator

The public workflow follows the pinned reference repository's layout:

```sh
lake exe cache get
LEAN_NUM_THREADS=1 lake build
lake env lean Check.lean
bash check-challenge.sh
LEAN_NUM_THREADS=1 lake comparator --config ComparatorChallenges/ConformalPoisson.json
```

The JSON configuration selects `ConformalPoisson.theorem_1_1`, compares
`ComparatorChallenges.ConformalPoisson` against `Solution`, permits only
`propext`, `Quot.sound`, and `Classical.choice`, and authorizes no definition
holes. It uses the comparator included with Lean/Lake 4.36.0-rc2. Nanoda and
the additional `--paranoid` checkers are not enabled by this configuration.

Lake independently builds and exports the two modules in its bubblewrap
sandbox, compares the target statement and its transitive defining constants,
checks the solution's reachable axioms, and replays its export through Lean's
default kernel checker. The stock comparator uses Lean's ordinary expression
comparison; this package does not alter that implementation. Its scope is the
configured theorem and its reachable definitions. The original release's
additional checks of all protected definitions and operational consumer use
are separately bound by the exact released-source manifests.

`Check.lean` imports the real consumer and prints the types and axioms of both
the main theorem and `ConformalPoisson.commonPointAndScale`. The frozen
challenge's `sorry` is a statement hole compiled in a separate environment;
neither `Solution` nor `Consumer` imports the challenge.

## Source identity

```sh
python3 scripts/check-sources.py
```

This checks the challenge and toolchain, all 817 released proof files, and all
253 canonical bundled Tau Ceti files against the recorded hashes. It also
rejects an added or missing Lean file in the released `Proof/` or canonical
`TauCeti/` sets. `check-challenge.sh` performs only the challenge and toolchain
part. This paper's challenge originated in the local commission, so the
script pins its ratified digest instead of fetching a different paper's
public challenge repository.

Source hashes establish identity relative to a trusted manifest; they do not
by themselves prove a theorem or make a modified manifest trustworthy. The
compiler, comparator, kernel replay, source reading, and human ratification
serve their separate roles.

## Pins and reproducibility

* Lean toolchain: `leanprover/lean4:v4.36.0-rc2`.
* Mathlib source: `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`.
* Tau Ceti source: `4d91513e4d30746eb1fa96658c18e051c772e55e`.
* Transitive dependencies: exact revisions in `lake-manifest.json`.

The original release also recorded digests of its nine compiled-library
inputs and its checker. These are retained as historical check provenance.
The public package builds the required Tau Ceti sources and same-revision
supplements from source against the locked Mathlib dependency; it does not
require access to the author's compiled-library directories.

For a source-only distribution, omit `.lake/`, `.git/`, and generated compiler
outputs. The supplied `.gitignore` excludes build artifacts and caches.
The [proof guide](PROOF_GUIDE.md) and
[mathematical expansion](expansion/README.md) describe the selected theorem's
scope and the two accepted proof-route departures.

## Package verification record

The package's own command results are recorded in
[`release/PACKAGE_CHECKS.json`](release/PACKAGE_CHECKS.json) after the standalone
build, theorem inspection, and sandboxed comparator have completed. They are
separate from the earlier authoritative release receipt.
