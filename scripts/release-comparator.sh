#!/usr/bin/env bash
# Release gate: install the pinned Comparator tools and run Comparator on every
# challenges/*/config.json, writing an attestation report to comparator-report/.
# Used by .github/workflows/release-comparator.yml on a fresh GitHub-hosted Linux runner.
#
# Usage: scripts/release-comparator.sh install|run
set -euo pipefail

# Immutable upstream source revisions. lean4export is built with this repository's exact
# lean-toolchain, since its olean reader must match the challenge toolchain. These revisions are
# also recorded in formalization.yaml (checked by scripts/check-formalization-manifest.rb).
COMPARATOR_REV=d03acab154d269c06e60e4de7e4cc85deebff94b
LANDRUN_REV=5ed4a3db3a4ad930d577215c6b9abaa19df7f99f
LEAN4EXPORT_REV=a3e35a584f59b390667db7269cd37fca8575e4bf
ROOT=$(git rev-parse --show-toplevel)
TOOLS="${RUNNER_TEMP:-/tmp}/comparator-tools"
REPORT="$ROOT/comparator-report"
mkdir -p "$REPORT/logs"

clone_pinned() {
  local url=$1 rev=$2 path=$3
  git clone --filter=blob:none "$url" "$path"
  git -C "$path" checkout --detach "$rev"
  test "$(git -C "$path" rev-parse HEAD)" = "$rev"
}

install() {
  mkdir -p "$TOOLS/bin"
  clone_pinned https://github.com/leanprover/comparator.git "$COMPARATOR_REV" "$TOOLS/comparator"
  clone_pinned https://github.com/leanprover/lean4export.git "$LEAN4EXPORT_REV" "$TOOLS/lean4export"
  clone_pinned https://github.com/zouuup/landrun.git "$LANDRUN_REV" "$TOOLS/landrun"
  cp "$ROOT/lean-toolchain" "$TOOLS/lean4export/lean-toolchain"
  (cd "$TOOLS/lean4export" && lake build lean4export)
  (cd "$TOOLS/comparator" && lake build comparator)
  (cd "$TOOLS/landrun" && go build -o "$TOOLS/bin/landrun" ./cmd/landrun)
  cp "$TOOLS/lean4export/.lake/build/bin/lean4export" "$TOOLS/bin/lean4export"
  cp "$TOOLS/comparator/.lake/build/bin/comparator" "$TOOLS/bin/comparator"
  "$TOOLS/bin/landrun" --version > "$REPORT/logs/landrun-version.txt" 2>&1 || true
}

run() {
  export COMPARATOR_LANDRUN="$TOOLS/bin/landrun"
  export COMPARATOR_LEAN4EXPORT="$TOOLS/bin/lean4export"
  export PATH="$TOOLS/bin:$PATH"
  python3 - "$ROOT" "$REPORT" "$TOOLS" "$COMPARATOR_REV" "$LANDRUN_REV" "$LEAN4EXPORT_REV" <<'PY'
import json, pathlib, subprocess, sys
root, report, tools = map(pathlib.Path, sys.argv[1:4])
comparator, landrun, lean4export = sys.argv[4:]
def out(*args): return subprocess.check_output(args, cwd=root, text=True).strip()
# The workflow validates this inventory against formalization.yaml
# (scripts/check-formalization-manifest.rb --metadata-only) before installing any tools.
configs = sorted(root.glob('challenges/*/config.json'))
if not configs:
    raise SystemExit('No challenge configurations found')
manifest = json.loads((root / 'lake-manifest.json').read_text())
data = {
    'commit': out('git', 'rev-parse', 'HEAD'),
    'tree': out('git', 'rev-parse', 'HEAD^{tree}'),
    'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
    'lean_version': out('lean', '--version'),
    'mathlib_revision': next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib'),
    'tools': {'comparator': comparator, 'landrun': landrun, 'lean4export': lean4export},
    'sandbox_note': (
        'Comparator is invoked with landrun on a standard GitHub-hosted Linux runner. Upstream '
        'documents a landrun sandbox caveat requiring systemd-run containment for a full '
        'adversarial guarantee; this workflow does not claim that stronger guarantee. Before '
        'Comparator runs, the workflow downloads the Mathlib cache and builds the trusted library '
        'and the trusted Challenge targets outside the sandbox; the challenge workspaces share '
        'that dependency folder read-only.'),
    'results': [],
}
def write(): (report / 'attestation.json').write_text(json.dumps(data, indent=2) + '\n')
write()
failed = False
for config in configs:
    cfg = json.loads(config.read_text())
    if sorted(cfg['permitted_axioms']) != ['Classical.choice', 'Quot.sound', 'propext']:
        raise SystemExit(f'Unexpected axiom allowance in {config}')
    name = config.parent.name
    with (report / 'logs' / f'{name}.log').open('w') as log:
        result = subprocess.run(['lake', 'env', str(tools / 'bin' / 'comparator'), str(config.resolve())],
                                cwd=config.parent, stdout=log, stderr=subprocess.STDOUT)
    ok = result.returncode == 0
    data['results'].append({
        'config': str(config.relative_to(root)), 'theorems': cfg['theorem_names'],
        'permitted_axioms': cfg['permitted_axioms'],
        'axiom_check': 'passed' if ok else 'failed', 'exit_code': result.returncode,
        'result': 'PASS' if ok else 'FAIL', 'log': f'logs/{name}.log'})
    write()
    failed |= not ok
    print(f'{name}: {"PASS" if ok else "FAIL"}', flush=True)
data['overall_result'] = 'FAIL' if failed else 'PASS'
write()
sys.exit(1 if failed else 0)
PY
}

case "${1:-}" in
  install) install ;;
  run) run ;;
  *) echo "usage: $0 install|run" >&2; exit 2 ;;
esac
