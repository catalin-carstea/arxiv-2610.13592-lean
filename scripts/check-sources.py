#!/usr/bin/env python3
"""Verify the frozen challenge, exact released proof, and bundled source files."""
from pathlib import Path
import argparse
import hashlib
import json
import sys

root = Path(__file__).resolve().parents[1]
parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument("--challenge-only", action="store_true")
args = parser.parse_args()

# These are the actual ratified reference bytes and its pinned toolchain text.
challenge = {
    "ComparatorChallenges/ConformalPoisson.lean":
        "36ced106db6002cdd84a26aaae0a2f45df1768cdd0d5afc45cff49af72142842",
}
manifest_path = root / "docs/release/CHALLENGE_SHA256.json"
recorded_challenge = json.loads(manifest_path.read_text())
if recorded_challenge.get(next(iter(challenge))) != next(iter(challenge.values())):
    sys.exit("challenge digest manifest differs from the ratified reference")
if (root / "lean-toolchain").read_bytes() != b"leanprover/lean4:v4.36.0-rc2\n":
    sys.exit("lean-toolchain differs from the ratified version")

def verify(label, manifest):
    for relative, expected in manifest.items():
        path = root / relative
        if path.is_symlink() or not path.is_file():
            sys.exit(f"missing or linked source: {relative}")
        actual = hashlib.sha256(path.read_bytes()).hexdigest()
        if actual != expected:
            sys.exit(f"source differs: {relative}")
    print(f"identical: {label} ({len(manifest)} files)")

verify("frozen challenge and toolchain", recorded_challenge)
if args.challenge_only:
    sys.exit(0)
proof = json.loads((root / "docs/release/SOURCE_SHA256.json").read_text())
actual_proof = {"Solution.lean", "Consumer.lean"} | {
    str(p.relative_to(root)) for p in (root / "Proof").rglob("*.lean")
}
if set(proof) != actual_proof:
    sys.exit("released proof source set differs from its manifest")
verify("ratified proof", proof)
upstream = json.loads((root / "docs/release/UPSTREAM_SHA256.json").read_text())
actual_upstream = {str(p.relative_to(root)) for p in (root / "TauCeti").rglob("*.lean")}
if set(upstream) != actual_upstream:
    sys.exit("bundled upstream source set differs from its manifest")
verify("bundled Tau Ceti", upstream)
