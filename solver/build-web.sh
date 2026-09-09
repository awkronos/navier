#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi

crate_dir="$(cd "$(dirname "$0")" && pwd)"
output_dir="$1"
wasm_bindgen="${WASM_BINDGEN:-wasm-bindgen}"

cd "$crate_dir"
cargo build --locked --release --target wasm32-unknown-unknown
mkdir -p "$output_dir"
"$wasm_bindgen" \
  --target web \
  --out-dir "$output_dir" \
  --out-name navier_web \
  target/wasm32-unknown-unknown/release/navier_web.wasm

python3 tools/write_provenance.py \
  --output-dir "$output_dir" \
  --rustc "$(rustc --version)" \
  --wasm-bindgen "$("$wasm_bindgen" --version)"
python3 tools/verify_web_build.py "$output_dir"
