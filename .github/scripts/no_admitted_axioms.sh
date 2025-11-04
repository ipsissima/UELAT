#!/usr/bin/env bash
set -euo pipefail

dir=${1:-Coq}

bash "$(dirname "$0")/check_coq_no_admitted.sh" "$dir"

