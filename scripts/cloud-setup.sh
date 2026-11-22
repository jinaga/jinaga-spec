#!/usr/bin/env bash
# Installs what scripts/verify.sh needs on a Claude Code cloud VM (Ubuntu, Node
# preinstalled, no Lean). Idempotent: a second run only checks.
#
# Runs two ways:
#   - from .claude/settings.json's SessionStart hook, on every cloud session;
#   - from the cloud environment's setup script, so the result is snapshotted
#     and later sessions start with it installed. Paste this as that script:
#
#       #!/bin/bash
#       s="$(find / -maxdepth 5 -path '*/jinaga-spec/scripts/cloud-setup.sh' 2>/dev/null | head -1)"
#       [ -z "$s" ] || bash "$s"
#
# A failed install fails the script, so a broken environment is never
# snapshotted as if it were ready.
#
# Locally (CLAUDE_CODE_REMOTE unset) it does nothing.
set -euo pipefail
[ "${CLAUDE_CODE_REMOTE:-}" = "true" ] || exit 0
cd "$(dirname "$0")/.."

# elan, pinned to a release tag rather than master (as verify.yml pins its
# actions). The toolchain itself comes from lean-toolchain.
ELAN_TAG=v4.2.4
if ! [ -x "$HOME/.elan/bin/elan" ]; then
  curl -sSfL "https://raw.githubusercontent.com/leanprover/elan/${ELAN_TAG}/elan-init.sh" \
    | sh -s -- -y --default-toolchain none
fi
export PATH="$HOME/.elan/bin:$PATH"
elan toolchain install "$(cat lean-toolchain)"
# verify.sh puts ~/.elan/bin on PATH itself; this makes lake and lean visible
# to every other command too, without relying on the session's environment.
[ -w /usr/local/bin ] && ln -sf "$HOME"/.elan/bin/* /usr/local/bin/

# The TypeScript port, and any checkout verify.sh or probe.mts will run against
# (sibling directories, or the JINAGA_JS / CASCADE_CORE / JINAGA_SERVER paths).
# npm ci deletes node_modules, so run it only when the lock file is newer than
# the last install.
install() {
  if [ "$1/package-lock.json" -nt "$1/node_modules/.package-lock.json" ]; then
    (cd "$1" && npm ci --silent)
  fi
}
install ports/typescript
for d in "${JINAGA_JS:-../jinaga.js}" "${CASCADE_CORE:-../jinaga-cascade-core}" "${JINAGA_SERVER:-../jinaga-server}"; do
  [ -f "$d/package-lock.json" ] && install "$d"
done
exit 0
