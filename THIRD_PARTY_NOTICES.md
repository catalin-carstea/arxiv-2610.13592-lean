# Third-party code and attribution

The formalization project authors are Cătălin I. Cârstea, Tony Liimatainen,
Yi-Hsuan Lin, and William Trad. This credit does not attribute upstream
library code to them. Original contributions are distributed under the
[BSD 3-Clause License](LICENSE); upstream material retains its existing terms.

## Tau Ceti

The 253 Lean files under [`TauCeti/`](TauCeti/) are unchanged copies from
[`TauCetiProject/TauCeti`](https://github.com/TauCetiProject/TauCeti/tree/4d91513e4d30746eb1fa96658c18e051c772e55e),
revision `4d91513e4d30746eb1fa96658c18e051c772e55e`. Their original copyright
and author notices are retained. These files are distributed under the
[Apache License, Version 2.0](TauCeti/LICENSE).
[`UPSTREAM_SHA256.json`](docs/release/UPSTREAM_SHA256.json) identifies every
bundled file and its exact bytes. Only the transitive source closure needed
by the released proof and challenge is bundled.

Another 568 files under `Proof/*/TauCeti/` are separately located supplements
from that same pinned source revision. Some have adapted imports, module
headers, elaboration options, or explicitly recorded local adaptations.
Their upstream copyright notices remain in the source, and the
[Tau Ceti Apache license](External/LICENSE.tauceti) is included separately.
The project also adopts attributed Tau Ceti arguments inside `Solution.lean`;
their source sections retain their authorship and adaptation notices.

## Mathlib

The 246 files under `Proof/*/Mathlib/` derive from
[`leanprover-community/mathlib4`](https://github.com/leanprover-community/mathlib4/tree/2ddf59c8f14245864e6c0ed227a2dab76b9efea2),
revision `2ddf59c8f14245864e6c0ed227a2dab76b9efea2`. They retain original
copyright and author notices and are distributed under the
[Apache License, Version 2.0](External/LICENSE.mathlib). Supplement imports
and elaboration settings may be adapted to the released import graph.

The per-file
[`SUPPLEMENT_ORIGINS.json`](docs/release/SUPPLEMENT_ORIGINS.json) identifies
all 814 upstream-derived supplement files, their original paths and source
hashes, and whether the packaged bytes differ from upstream. Of these, 148
are byte-for-byte copies and 666 are marked as adapted. These declarations
retain their upstream names; putting them under a `Proof/` module path does
not change their authorship. The supplement manifests identify the exact
released source rather than suggesting that the supplements are newly
authored project mathematics.

The main Mathlib dependency and its transitive packages are fetched at the
revisions in [`lake-manifest.json`](lake-manifest.json). Their own sources,
copyright notices, and licenses are supplied by those packages. The
supplements make additional same-revision source results available without
changing the original release's external compiled-library inputs.

## Earlier anisotropic Calderón formalization

`Solution.lean` contains an explicitly attributed finite-jet argument adapted
from Cătălin I. Cârstea and Lauri Oksanen's
[`anisotropic-calderon-lean`](https://github.com/catalin-carstea/anisotropic-calderon-lean/tree/0f09786282d0f2d3865fa0f175b63c35969d25f7),
revision `0f09786282d0f2d3865fa0f175b63c35969d25f7`.
Its [original BSD 3-Clause license](External/LICENSE.calderon) is preserved,
including both original copyright holders. The package documentation and
comparator layout also follow that repository. The formalized paper and
geometric claim here are distinct from its Euclidean-ball Calderón theorem.

## Lean and tooling

Lean and Lake are developed by their respective contributors and distributed
separately through the toolchain named in `lean-toolchain`. This package uses
Lake's unmodified comparator. It does not redistribute a Lean toolchain or
dependency build cache. The small project-specific `Proof/ProofInfo.lean`
elaboration command is part of the released project proof support.

## Selected mathematical source

The selected statement is Theorem 1.1 of
[*The conformal Poisson embedding method for the anisotropic Calderón problem
with a potential*](https://arxiv.org/abs/2610.13592v1), by Cătălin I. Cârstea,
Tony Liimatainen, Yi-Hsuan Lin, and William Trad. Citation metadata is in
[`CITATION.cff`](CITATION.cff). The frozen translation and the public proof
expansion are included; the original manuscript archive and private workflow
records are not redistributed in this source package.
