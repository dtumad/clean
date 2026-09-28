#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."

out="${1:-.lake/build/construction-pilot}"
mkdir -p "$out"
out="$(cd "$out" && pwd)"
export PATH="$PWD/.lake/test-tools/node_modules/.bin:$PATH"
export LEAN_NUM_THREADS="${LEAN_NUM_THREADS:-2}"

# Clean's backend tests print SKIP when these tools are absent. Require them here.
for tool in node snarkjs wasm-validate wasm2wat; do
  command -v "$tool" >/dev/null || { echo "Missing required test tool: $tool" >&2; exit 1; }
done

{
  date -u '+UTC=%Y-%m-%dT%H:%M:%SZ'
  git rev-parse HEAD
  git status --porcelain
  lake env lean --version
  node --version
  node -p "require('./.lake/test-tools/node_modules/snarkjs/package.json').version"
  wasm-validate --version
  cat lean-toolchain
  cat lake-manifest.json
  echo "Build cache may be reused; this runner does not claim a cold build."
} > "$out/provenance.txt"

run() {
  local label="$1"
  shift
  printf '%s:' "$label" >> "$out/commands.txt"
  printf ' %q' "$@" >> "$out/commands.txt"
  printf '\n' >> "$out/commands.txt"
  local result=0
  local started=$SECONDS
  "$@" > "$out/$label.log" 2>&1 || result=$?
  cat "$out/$label.log"
  printf '%s exit=%s elapsed_seconds=%s\n' "$label" "$result" "$((SECONDS - started))" >> "$out/commands.txt"
  return "$result"
}

: > "$out/commands.txt"
run build lake build --no-cache --wfail Clean Clean.Utils.Test.TestConstruction
run tests lake build --no-cache CleanTests
if grep -q 'SKIP:' "$out/build.log" "$out/tests.log"; then
  echo "A cached or fresh backend test was skipped; rerun that test with tools available." >&2
  exit 1
fi
# The pinned upstream tactic smoke tests deliberately end ten examples in `sorry`.
# Keep that file byte-identical and allow only those exact diagnostics in CleanTests.
git diff --exit-code fba2a29f5e36420d797c1de118ac9f11f23b819e -- \
  Clean/Utils/Test/TestCircuitProofStart.lean
python3 - "$out/tests.log" <<'PY'
import pathlib
import sys

allowed = {
    f"warning: Clean/Utils/Test/TestCircuitProofStart.lean:{line}:0: declaration uses `sorry`"
    for line in (20, 32, 43, 52, 61, 74, 91, 132, 160, 186)
}
warnings = [line for line in pathlib.Path(sys.argv[1]).read_text().splitlines()
            if line.startswith("warning:")]
unexpected = set(warnings) - allowed
if unexpected:
    sys.exit("Unexpected CleanTests diagnostics:\n" + "\n".join(sorted(unexpected)))
print(f"CleanTests: {len(warnings)} existing tactic smoke-test warnings; no new warnings")
PY
run cases lake env lean --run scripts/constructionPilot.lean
run statements lake env lean scripts/constructionReport.lean
python3 - "$out/statements.log" <<'PY'
import pathlib
import re
import sys

reports = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",
                     pathlib.Path(sys.argv[1]).read_text())
if len(reports) != 20:
    sys.exit(f"Expected 20 axiom reports, found {len(reports)}")
for name, axioms in reports:
    unexpected = set(axioms.split(", ")) - {"propext", "Classical.choice", "Quot.sound"}
    if unexpected:
        sys.exit(f"Unexpected axioms for {name}: {unexpected}")
print("PASS: 20 construction statements use only standard logical axioms")
PY
run imports lake env lean scripts/constructionImports.lean
run style python3 scripts/check-consecutive-empty-lines.py
echo "PASS: construction pilot validation"
