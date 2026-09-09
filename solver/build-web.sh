#!/usr/bin/env bash
set -euo pipefail

if [[ $# -ne 1 ]]; then
  echo "usage: $0 OUTPUT_DIRECTORY" >&2
  exit 2
fi

crate_dir="$(cd "$(dirname "$0")" && pwd)"
output_dir="$1"
wasm_bindgen="${WASM_BINDGEN:-wasm-bindgen}"

# Rust embeds source locations in panic and diagnostic strings.  Give each
# machine-dependent source root a stable virtual name before compiling so the
# browser artifact is relocatable and cannot disclose the builder's home path.
home_dir="$(cd "${HOME:?HOME must be set}" && pwd -P)"
cargo_home="$(cd "${CARGO_HOME:-$HOME/.cargo}" && pwd -P)"
rust_sysroot="$(rustc --print sysroot)"
remap_flags=(
  "--remap-path-prefix=$crate_dir=/navier-source"
  "--remap-path-prefix=$cargo_home=/cargo-source"
  "--remap-path-prefix=$rust_sysroot=/rust-toolchain"
  "--remap-path-prefix=$home_dir=/build-home"
)
encoded_rustflags=""
for flag in "${remap_flags[@]}"; do
  [[ -z "$encoded_rustflags" ]] || encoded_rustflags+=$'\x1f'
  encoded_rustflags+="$flag"
done
export CARGO_ENCODED_RUSTFLAGS="$encoded_rustflags"
unset RUSTFLAGS
export CARGO_INCREMENTAL=0

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
