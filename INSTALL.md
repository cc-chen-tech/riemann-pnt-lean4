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
leanprover/lean4:v4.29.1
```

### 2. Clone and Build

```bash
git clone https://github.com/cc-chen-tech/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

Current local development uses a path dependency:

```lean
require mathlib from "./vendor/mathlib"
```

The `vendor/mathlib` directory is intentionally ignored by git because it is
large. To reproduce this exact local setup, place Mathlib 4.29.1 at
`vendor/mathlib` before running `lake build`.

For a public release, `lakefile.lean` should be switched back to a pinned git
dependency on Mathlib 4.29.1 and `lake-manifest.json` regenerated. The local
path dependency is a build-stability workaround, not a release-ready dependency
configuration.

### 3. Explore in VS Code

Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
for VS Code. Open the project folder and you'll get interactive theorem proving
with inline goal displays.

## System Requirements

- 8+ GB RAM recommended (Mathlib is large)
- 10+ GB free disk space, more if keeping a local `vendor/mathlib` checkout
- macOS, Linux, or Windows (via WSL2)

## Troubleshooting

If `lake build` fails with memory errors, try:

```bash
lake build -- --old  # use single-threaded compilation
```
