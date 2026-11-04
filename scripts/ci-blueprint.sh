#!/usr/bin/env bash
set -euo pipefail
export PATH="$HOME/.elan/bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-8}"
export PYTHONDONTWRITEBYTECODE=1
cd "$(dirname "$0")/.."
mkdir -p _out/audit
lake build
lake exe vbp build
lake exe vbp query work-queue > _out/audit/work-queue.json
lake exe vbp query metadata > _out/audit/metadata.json
lake exe vbp check
python3 scripts/audit_blueprint.py
python3 scripts/audit_statement_links.py
python3 scripts/run_lean_audit.py audit/checks/Statements.lean
python3 scripts/run_lean_audit.py audit/checks/Interfaces.lean
python3 scripts/run_lean_audit.py audit/checks/Associations.lean
python3 scripts/phase1_audit.py --prepare
lake env lean _out/audit/Environment.lean > _out/audit/environment-stdout.txt
python3 scripts/phase1_audit.py
python3 scripts/run_lean_audit.py audit/checks/ExplicitParameters.lean
python3 scripts/run_lean_audit.py audit/checks/DependencyClosure.lean
python3 scripts/run_lean_audit.py audit/checks/StatementExamples.lean
python3 scripts/check_snapshot.py
python3 scripts/check_blueprint_site.py
