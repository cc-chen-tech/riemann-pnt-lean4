# Global e primitive resonance implementation plan

> **For agentic workers:** Use the existing approved research execution flow;
> independent review is read-only. Do not launch another implementation worker.

**Goal:** Record the all-e primitive Fourier representation and prove only its
exact-resonant subterm meets the balanced top budget.

**Architecture:** Start at GU4 with q=1 and U=1, restore all artificial
partitions, set M=Ae and B=eb, and retain both resulting Möbius weights.
Separate the primitive determinant zero from its signed complement.

**Tech Stack:** Self-contained mathematics, Python Fraction, pytest.

**Spec:** `docs/research/2026-08-30-mwkf-general-unit-type-ii.md`,
`docs/research/2026-08-30-mwkf-joint-type-ii-density.md`, and the approved
current-turn all-e resonance derivation.

## Global constraints

- q=1 and R=S=T^3, HL≈T^5, K≈P≈Z≈T only for the analytic conclusion.
- New Fourier h is not the original hδ label or canonical zero Gram.
- Nonzero determinant, original q reassembly, both reflection mixed terms,
  and independent physical tails remain obligations.
- Use the existing isolated branch; update PR490 without merging.

## Single deliverable: proof and independently checked finite adapter

Files: add `tests/test_mwkf_global_e_primitive.py`, extend
`scripts/mwkf_physical_type_ramanujan.py`, add
`docs/research/2026-08-30-mwkf-global-e-primitive-resonance.md`, and update
§9.213 plus the status header in the main research note.

Interfaces: `mobius_u_one_ledger(n,Q)` retains the n=1 endpoint;
`global_e_primitive_packet(M,B,j,k,l,ns,amplitude)` compares literal all-v
coefficients with the common-n fused coefficients;
`primitive_resonant_rows(M,j,kl,Bmax)` enumerates the exact divisor family;
`primitive_band_rows(M,B,j,kl,H)` retains every primitive integer in a
finite rational frequency window.

- [x] Write tests independently enumerating original allocations, including
  the hand fixture M=6,B=30 -> e=6,A=1,b=5 and coefficient -1/180 at n=1.
  Include n=1, nonsquarefree quotient, both phase signs, shared j primes,
  nonprimitive exclusions and the nonzero determinant -1 example.
- [x] Run the new pytest module; missing named functions must fail.
- [x] Implement only those finite interfaces with integer-domain validation.
- [x] Run the new module and existing GU/JT/JQ tests.
- [x] Write the exact symbol, Fourier tail, resonance proof and T^5 unsigned
  complement ledger; compare BC's determinant input without claiming transfer.
- [x] Obtain independent review; run the available full Python suite, Ruff
  E9,F63,F7,F82 and git diff --check. Record actual exclusions and exit codes.
- Release action: commit and push exactly the reviewed files, refresh PR490 live, retain
  its historical body and non-Draft status; leave the mathematical goal active.

Verification before release: 33 new tests failed for the missing functions,
then all passed; the available full suite returned 1252 passed, 1 skipped
in 41.39s. Two existing Flint-dependent modules were excluded. Focused Ruff
E9,F63,F7,F82 and git diff --check passed. Independent mathematical/code
review found no Critical/Important defects; the full analytic gate is open.
