#!/bin/bash
# Reality project Lean build lock — STRICTER than global reform.
#
# Root cause (2026-08-08): global lock treats `lake env lean` as lock-free, but
# missing oleans make `lake env lean` WRITE into `.lake/build`. Swarm agents
# then race-compile the same deps (e.g. G2SplitDerivations) → oleans never
# stabilize → LSP "imports out of date" / missing olean storms.
#
# Lock key bug (2026-08-23): this script is also the absolute symlink target for
# Fermat and Tao. Its fixed Reality lock therefore serialized three unrelated
# output roots. Keep the stricter single-file policy, but key that lock to the
# invoking repository. Full builds delegate to the canonical output-set wrapper
# so path dependencies also serialize on every directory they can write.
TIMEOUT=${1:-300}
shift
CMD="$*"

if [[ "$CMD" == *"lake build"* || "$CMD" == make\ proof* ]]; then
  exec "${HOME}/.claude/hooks/lean-build-lock.sh" "$TIMEOUT" "$@"
fi

if [[ "$CMD" == lake\ * || "$CMD" == *" lake "* ]]; then
  ROOT=$(git rev-parse --show-toplevel 2>/dev/null || true)
  if [[ -z "$ROOT" ]]; then
    echo "ERROR: cannot resolve project root for Lean build lock" >&2
    exit 1
  fi
  KEY=$(printf '%s' "$ROOT" | shasum | cut -c1-12)
  LOCKFILE="/tmp/lean-build-${KEY}.lock"
  exec 200>"$LOCKFILE"
  if ! flock -w "$TIMEOUT" 200; then
    echo "ERROR: project Lean lock busy after ${TIMEOUT}s (${LOCKFILE})" >&2
    echo "ERROR: another lake/env-lean holds .lake/build — wait or kill thrashers" >&2
    exit 1
  fi
  echo "[lean-build-lock] acquired ${LOCKFILE} for: $CMD" >&2
  "$@"
  rc=$?
  echo "[lean-build-lock] released ${LOCKFILE} rc=${rc}" >&2
  exit $rc
fi
exec "$@"
