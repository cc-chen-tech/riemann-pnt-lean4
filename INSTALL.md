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

### 2. Clone and Build

```bash
git clone https://github.com/cc-chen-tech/riemann-pnt-lean4.git
cd riemann-pnt-lean4
lake build
```

The first build will download and compile Mathlib, which can take 30-60 minutes
depending on your machine.

### 3. Explore in VS Code

Install the [Lean 4 extension](https://marketplace.visualstudio.com/items?itemName=leanprover.lean4)
for VS Code. Open the project folder and you'll get interactive theorem proving
with inline goal displays.

## System Requirements

- 8+ GB RAM recommended (Mathlib is large)
- 10+ GB free disk space
- macOS, Linux, or Windows (via WSL2)

## Troubleshooting

If `lake build` fails with memory errors, try:

```bash
lake build -- --old  # use single-threaded compilation
```
