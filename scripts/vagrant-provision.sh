#!/usr/bin/env bash
# One-shot provisioning for a fresh Vagrant VM (not intended for re-runs).
set -euo pipefail
export DEBIAN_FRONTEND=noninteractive

JULIA_SERIES="$(printf '%s' "${JULIA_VERSION}" | cut -d. -f1-2)"
JULIA_INSTALL_DIR="/opt/julia-${JULIA_VERSION}"

apt-get update
apt-get install -y \
  build-essential \
  ca-certificates \
  cmake \
  curl \
  git \
  gfortran \
  net-tools \
  nodejs \
  npm \
  pipx \
  pkg-config \
  python3-pip \
  python3-venv \
  rubber \
  rsync \
  texlive-bibtex-extra \
  texlive-fonts-recommended \
  texlive-latex-base \
  texlive-latex-extra \
  texlive-latex-recommended \
  tmux \
  unzip \
  xz-utils \
  zstd

chown -R vagrant:vagrant /agent-workspace

# Julia system-wide from official binaries.
arch="$(dpkg --print-architecture)"
case "${arch}" in
  amd64)
    julia_url_arch="x64"
    julia_tar_arch="x86_64"
    ;;
  arm64)
    julia_url_arch="aarch64"
    julia_tar_arch="aarch64"
    ;;
  *)
    echo "Unsupported architecture for Julia: ${arch}" >&2
    exit 1
    ;;
esac

julia_tarball="julia-${JULIA_VERSION}-linux-${julia_tar_arch}.tar.gz"
julia_url="https://julialang-s3.julialang.org/bin/linux/${julia_url_arch}/${JULIA_SERIES}/${julia_tarball}"
tmp_julia_tarball="/tmp/${julia_tarball}"

curl -fsSL "${julia_url}" -o "${tmp_julia_tarball}"
rm -rf "${JULIA_INSTALL_DIR}"
tar -xzf "${tmp_julia_tarball}" -C /opt
rm -f "${tmp_julia_tarball}"
ln -sfn "${JULIA_INSTALL_DIR}/bin/julia" /usr/local/bin/julia

# elan + Lean toolchain pinned by this project (/agent-workspace = repo root).
sudo -u vagrant -H bash -lc 'curl -fsSL https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh | sh -s -- -y --default-toolchain none'

toolchain_file="/agent-workspace/lean-toolchain"
if [ -f "${toolchain_file}" ]; then
  toolchain="$(tr -d '[:space:]' < "${toolchain_file}")"
  if [ -n "${toolchain}" ]; then
    sudo -u vagrant -H env LEAN_TOOLCHAIN="${toolchain}" bash -lc 'export PATH="$HOME/.elan/bin:$PATH"; elan toolchain install "$LEAN_TOOLCHAIN"'
    sudo -u vagrant -H env LEAN_TOOLCHAIN="${toolchain}" bash -lc 'export PATH="$HOME/.elan/bin:$PATH"; elan default "$LEAN_TOOLCHAIN"'
  fi
fi

npm install -g @openai/codex

# Codex Stop hook for session continuation (active only when CODEX_KEEPALIVE=1).
# See https://www.chenyang.co/blog/agents/2026/04/16/codex-continuation.html
install -d -m 755 -o vagrant -g vagrant /home/vagrant/.codex/hooks

cat > /home/vagrant/.codex/config.toml <<'EOF'
[features]
codex_hooks = true
EOF

cat > /home/vagrant/.codex/hooks.json <<'EOF'
{
  "hooks": {
    "Stop": [
      {
        "hooks": [
          {
            "type": "command",
            "command": "python3 /home/vagrant/.codex/hooks/keep_session_alive.py",
            "timeout": 5,
            "statusMessage": "Evaluating keep-alive hook"
          }
        ]
      }
    ]
  }
}
EOF

cat > /home/vagrant/.codex/hooks/keep_session_alive.py <<'EOF'
#!/usr/bin/env python3
"""Codex Stop hook: continuation prompt when CODEX_KEEPALIVE=1."""

import json
import os
import subprocess
import sys

ENABLE_ENV = "CODEX_KEEPALIVE"
PROMPT_ENV = "CODEX_KEEPALIVE_PROMPT"
SCRIPT_ENV = "CODEX_KEEPALIVE_SCRIPT"
DEFAULT_PROMPT = (
    "Continue working in this session without waiting for the user. "
    "Do another pass: verify the latest result, look for the next "
    "concrete action, and keep going."
)


def main() -> int:
    if not os.getenv(ENABLE_ENV):
        return 0

    json.load(sys.stdin)

    script = os.getenv(SCRIPT_ENV)
    if script:
        result = subprocess.run(script, shell=True)
        if result.returncode == 0:
            return 0

    json.dump(
        {
            "decision": "block",
            "reason": os.getenv(PROMPT_ENV, DEFAULT_PROMPT),
        },
        sys.stdout,
    )
    sys.stdout.write("\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
EOF

chmod 755 /home/vagrant/.codex/hooks/keep_session_alive.py
chown -R vagrant:vagrant /home/vagrant/.codex

cat > /etc/profile.d/agent-workspace-env.sh <<'EOF'
export ELAN_HOME=/home/vagrant/.elan

if [ -d /home/vagrant/.elan/bin ]; then
  export PATH="/home/vagrant/.elan/bin:$PATH"
fi
EOF
chmod 644 /etc/profile.d/agent-workspace-env.sh

julia --version
rubber --version
sudo -u vagrant -H bash -lc 'export PATH="$HOME/.elan/bin:$PATH"; cd /agent-workspace && lean --version && lake --version'
