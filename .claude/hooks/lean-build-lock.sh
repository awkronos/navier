#!/bin/bash
# Repo forwarder for the estate Lean build lock.
#
# Single source of truth: ~/.claude/hooks/lean-build-lock.sh. That owner holds
# the whole policy: the output-keyed full-build lock (path dependencies
# included), the satellite full-build cap, the memory refusals, numeric-or-not
# timeout parsing, and the .lake/packages symlink preflight that keeps a lake
# re-resolution from deleting the shared Mathlib cache. This file only forwards,
# so repo-relative callers (`bash .claude/hooks/lean-build-lock.sh 300 lake ...`)
# keep working. Never add policy here; change the owner.
#
# STOR1012-SSOT-M (2026-10-12): this forwarder replaced per-repo copies that had
# drifted into eight variants. Copies of the old Reality single-file lock ran
# `lake env lean` without the symlink preflight, and copies of the flat lock ran
# `lake build` without the build cap or memory refusals. Every repo that ships
# this forwarder ships these exact bytes.
OWNER="${HOME}/.claude/hooks/lean-build-lock.sh"
if [ -f "$OWNER" ]; then
  exec bash "$OWNER" "$@"
fi
echo "lean-build-lock: owner ${OWNER} is missing on $(hostname -s); running without the estate lock" >&2
if [[ "${1:-}" =~ ^[0-9]+$ ]]; then shift; fi
exec "$@"
