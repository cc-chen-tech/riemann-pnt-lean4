# Installation Guide

## Prerequisites

### 1. Install Lean 4 and Elan

[Elan](https://github.com/leanprover/elan) is the Lean version manager (like `rustup` for Rust).

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh
```

Verify installation:

```bash
lean --version
lake --version
```

This repository is pinned by `lean-toolchain` to:

```text
leanprover/lean4:v4.33.0-rc2
```

### 2. Prepare `vendor/mathlib`

`lakefile.lean` uses a local path dependency:

```lean
require mathlib from "./vendor/mathlib"
```

The `vendor/mathlib` directory is intentionally ignored by git (it is large).
Before building, place a Mathlib checkout at the exact pinned commit
`51e6992efd06126df61a496bebf8f49482a4e129` (tag `v4.33.0-rc2`):

```bash
git clone https://github.com/leanprover-community/mathlib4 vendor/mathlib
cd vendor/mathlib
git checkout 51e6992efd06126df61a496bebf8f49482a4e129
# optional but strongly recommended: download prebuilt oleans (~9 GB)
lake exe cache get
cd ../..
```

If you already have another checkout of this repository (e.g. a worktree)
with `vendor/mathlib` prepared, copying the whole `vendor/mathlib` directory
(including its `.lake`, which holds the olean cache) also works and avoids
redownloading.

The vendored `Zeta23/` library is tracked by git (it comes with the clone);
its provenance and license are recorded in
`docs/research/zeta23-merge-provenance.md`.

### 3. Clone and Build

```bash
git clone https://github.com/cc-chen-tech/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

To limit parallel compilation (useful on machines with limited memory):

```bash
lake build -K jobs=2
```

For a public release, `lakefile.lean` should be switched back to a pinned git
dependency on Mathlib `v4.33.0-rc2` and `lake-manifest.json` regenerated. The
local path dependency is a build-stability workaround, not a release-ready
dependency configuration.

### 4. Explore in VS Code

Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
for VS Code. Open the project folder and you'll get interactive theorem proving
with inline goal displays.

## System Requirements

- 8+ GB RAM recommended (Mathlib is large)
- 25+ GB free disk space if building Mathlib locally (olean cache ~9 GB);
  10+ GB if using a copied `vendor/mathlib` with a prebuilt cache
- macOS, Linux, or Windows (via WSL2)

## Troubleshooting

If `lake build` fails with memory errors, try:

```bash
lake build -- --old  # use single-threaded compilation
```
