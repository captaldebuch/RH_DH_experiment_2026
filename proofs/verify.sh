#!/usr/bin/env bash
set -euo pipefail

cd "$(git rev-parse --show-toplevel)"

lake build
lake env lean proofs/NBMellinTools/Audit.lean
