#!/usr/bin/env sh
# Build the standalone comparator workspaces from a fixed, reviewed list.
#
# Adapted from viscosity-solution-theory v0.2.0, scripts/build-challenges.sh.
#
# `--challenge-only` is appropriate before a Comparator release run: it never
# elaborates untrusted Solution.lean files. `--trusted-all` is for local
# development after the whole checkout is trusted.
#
# Environment:
#   LAKE         the lake command (default `lake`), e.g. a wrapper that
#                throttles concurrent builds.
#   FETCH_CACHE  set to 1 to run `lake exe cache get` at the root first (CI);
#                development checkouts clone the Mathlib build instead.
set -eu

usage() {
  cat <<'EOF'
Usage: scripts/build-challenges.sh --challenge-only|--trusted-all

  --challenge-only  Build only the trusted Challenge target in every workspace.
  --trusted-all     Build Challenge and Solution explicitly in every workspace.

Use --challenge-only before an adversarial Comparator run.  --trusted-all is
only for a reviewed, trusted checkout.
EOF
}

if [ "$#" -ne 1 ]; then
  usage >&2
  exit 2
fi

case "$1" in
  --challenge-only) build_solution=false ;;
  --trusted-all) build_solution=true ;;
  --help|-h)
    usage
    exit 0
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac

LAKE=${LAKE:-lake}

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

# Deliberately enumerate release workspaces instead of discovering arbitrary
# directories: this driver is part of the reviewed release configuration.
workspaces='
main-theorem
planar-structure
model-cases'

# Fail closed if a new configured workspace has not been added to the reviewed
# allowlist above.  This catches coverage drift without executing arbitrary
# workspace configuration.
for config in "$repo_root"/challenges/*/config.json; do
  workspace=${config%/config.json}
  workspace=${workspace##*/}
  listed=false
  for reviewed_workspace in $workspaces; do
    if [ "$workspace" = "$reviewed_workspace" ]; then
      listed=true
      break
    fi
  done
  if [ "$listed" = false ]; then
    echo "Unreviewed challenge workspace is missing from the driver: $workspace" >&2
    exit 1
  fi
done

for workspace in $workspaces; do
  workspace_dir="$repo_root/challenges/$workspace"
  for required_file in Challenge.lean Solution.lean config.json lakefile.toml; do
    if [ ! -f "$workspace_dir/$required_file" ]; then
      echo "Missing $required_file in challenge workspace: $workspace_dir" >&2
      exit 1
    fi
  done
done

# Every workspace sets `packagesDir = "../../.lake/packages"`, so all of them
# share the root workspace's dependency checkouts and builds (the manifests
# lock identical revisions).
if [ "${FETCH_CACHE:-0}" = 1 ]; then
  echo "==> root: dependency cache"
  (
    cd "$repo_root"
    lake exe cache get
  )
fi

for workspace in $workspaces; do
  workspace_dir="$repo_root/challenges/$workspace"
  # A workspace in the Statement.lean layout builds its trusted Statement module first.
  if [ -f "$workspace_dir/Statement.lean" ]; then
    echo "==> $workspace: Statement"
    (
      cd "$workspace_dir"
      $LAKE build Statement
    )
  fi
  echo "==> $workspace: Challenge"
  (
    cd "$workspace_dir"
    $LAKE build Challenge
  )
done

if [ "$build_solution" = true ]; then
  for workspace in $workspaces; do
    workspace_dir="$repo_root/challenges/$workspace"
    echo "==> $workspace: Solution"
    (
      cd "$workspace_dir"
      $LAKE build Solution
    )
  done
fi
