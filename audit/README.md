# Audit data

This directory contains the mapping from targets to declarations, the register of classical premises, proof dependencies, source checksums, and rerunnable audit programs.
Start with the [target table](../docs/TARGETS.md), [classical results](../docs/CLASSICAL_RESULTS.md), and [remaining infrastructure](../docs/INFRASTRUCTURE.md).

Run `./scripts/ci-blueprint.sh` to repeat the checks. Output is written to `_out/audit/`.
`#print axioms` does not expose every condition supplied as a parameter; theorem types and structure fields must also be inspected.
