#!/usr/bin/env bash
#
# Install the two ACL2-assist tools used in this devcontainer:
#
#   1. ACL2 MCP server  (https://github.com/jimwhite/acl2-mcp)
#        - Python MCP server exposing ACL2 tools (prove, evaluate, certify_book, ...)
#        - Installed into a venv at $HOME/.venvs/acl2-mcp
#        - Launched via the `acl2-mcp` executable in that venv
#
#   2. parinfer-rust CLI (https://github.com/eraserhd/parinfer-rust)
#        - Structural Lisp editing helper (indent / paren modes)
#        - Installed via `cargo install` from GitHub (not on crates.io)
#
# This script is idempotent: re-running it is safe.
#
# It runs as the container's remoteUser (jovyan), so everything is
# installed under $HOME (no root needed).

set -euo pipefail

log() { printf '\n\033[1;34m==> %s\033[0m\n' "$*"; }

# ---------------------------------------------------------------------------
# 1. ACL2 MCP server
# ---------------------------------------------------------------------------
install_acl2_mcp() {
    local venv="$HOME/.venvs/acl2-mcp"
    local src="$HOME/.local/src/acl2-mcp"

    if [ -x "$venv/bin/acl2-mcp" ]; then
        log "ACL2 MCP already installed at $venv/bin/acl2-mcp"
        return
    fi

    log "Installing ACL2 MCP server..."

    # Python 3.10+ is required.
    if ! command -v python3 >/dev/null 2>&1; then
        echo "ERROR: python3 not found" >&2
        exit 1
    fi

    # Clone the repo (shallow) if not already present.
    if [ ! -d "$src" ]; then
        mkdir -p "$(dirname "$src")"
        git clone --depth 1 https://github.com/jimwhite/acl2-mcp.git "$src"
    fi

    # Create a venv and install the package.
    python3 -m venv "$venv"
    "$venv/bin/pip" install --upgrade pip
    "$venv/bin/pip" install -e "$src"

    # Sanity check.
    if [ ! -x "$venv/bin/acl2-mcp" ]; then
        echo "ERROR: acl2-mcp executable not found after install" >&2
        exit 1
    fi
    log "ACL2 MCP installed: $venv/bin/acl2-mcp"
}

# ---------------------------------------------------------------------------
# 2. parinfer-rust CLI
# ---------------------------------------------------------------------------
install_parinfer() {
    local cargo_env="$HOME/.cargo/env"

    if command -v parinfer-rust >/dev/null 2>&1; then
        log "parinfer-rust already installed: $(command -v parinfer-rust)"
        return
    fi

    log "Installing Rust toolchain (if needed)..."

    # Install Rust if cargo is not present.
    if [ ! -f "$cargo_env" ] && ! command -v cargo >/dev/null 2>&1; then
        curl https://sh.rustup.rs -sSf | sh -s -- -y
    fi

    # Source cargo env for this shell.
    # shellcheck disable=SC1090
    [ -f "$cargo_env" ] && . "$cargo_env"

    log "Installing parinfer-rust from GitHub..."
    cargo install --git https://github.com/eraserhd/parinfer-rust

    # Sanity check.
    if ! command -v parinfer-rust >/dev/null 2>&1; then
        echo "ERROR: parinfer-rust not found after install" >&2
        exit 1
    fi
    log "parinfer-rust installed: $(command -v parinfer-rust)"
}

# ---------------------------------------------------------------------------
# Main
# ---------------------------------------------------------------------------
install_acl2_mcp
install_parinfer

log "All tools installed."
log "ACL2 MCP:      $HOME/.venvs/acl2-mcp/bin/acl2-mcp"
log "parinfer-rust: $(command -v parinfer-rust)"
