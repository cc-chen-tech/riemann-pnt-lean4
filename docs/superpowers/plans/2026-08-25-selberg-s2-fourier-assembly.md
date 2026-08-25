# Selberg S2 Fourier Assembly Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:executing-plans to implement this plan task-by-task.

**Goal:** Assemble the already proved residue and nonconstant positive-frequency mass bounds into the genuine sliding-window second-moment estimate, with Mathlib's exact `2*pi` Fourier normalization.

**Architecture:** Keep the proof in three independently checked layers.  First combine the explicit kernel decomposition `f = R + N` with `|R+N|^2 <= 2|R|^2 + 2|N|^2` on positive frequencies.  Second prove the negative-frequency energy equals the positive-frequency energy because `selbergCompletedMollifiedFComplex` is real-valued, and transport `y = 2*pi*w` with the exact Jacobian.  Third invoke the existing rectangular-multiplier theorem with `H = 2*pi/L`, where `L = log (X^a)`, and absorb constants into the S2 scale.

**Tech Stack:** Lean 4.33, Mathlib Bochner/set integrals and L2 Fourier transform, existing Selberg S1 and low/high mass modules, repository contract tests.

**Spec:** `docs/research/2026-08-24-selberg-mainline-mathematical-audit.md`, equations `(S2-Plancherel)`, `(S2-res-low)`, and `(S2-res-high)`.

## Global Constraints

- Do not use Zeta23 or a zero-density input.
- Do not add `sorry`, `admit`, `axiom`, or `opaque`.
- Prove the real-Fourier symmetry from the actual real-valued completed mollified function; do not assume a separate theta-kernel symmetry.
- Preserve the exact Mathlib normalization `Fhat(w) = sqrt(2*pi) * f(2*pi*w)`.
- Use the consistent window `H = 2*pi / L`; the older paper occurrence `H = 1/L` belongs to angular-frequency normalization and must not be mixed with Mathlib frequency.
- Write every public contract before its implementation and observe the expected missing-declaration failure.

---

### Task 1: Positive-frequency explicit-kernel mass

**Files:**
- Create: `HardyTheorem/SelbergExplicitFourierMass.lean`
- Create: `Test/SelbergExplicitFourierMassContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `selbergExplicitInverseFourierKernel_eq_residue_add_nonconstant` and the residue/nonconstant low/high mass bounds.
- Produces: a pointwise norm-square inequality and positive low/high integral bounds at the common scale.

- [x] Write the failing contract and verify RED.
- [x] Prove `normSq (R+N) <= 2*normSq R + 2*normSq N`.
- [x] Establish the required integrability on `Ioc 0 L` and `Ioi L` and integrate the pointwise inequality.
- [x] Combine the two existential constants uniformly and verify GREEN.

### Task 2: Real Fourier symmetry and exact `2*pi` transport

**Files:**
- Create or modify: `MathlibAux/RealFourierEnergySymmetry.lean`
- Create: `Test/RealFourierEnergySymmetryContract.lean`
- Modify: `HardyTheorem/SelbergExplicitFourierMass.lean`

**Interfaces:**
- Consumes: real-valuedness of `selbergCompletedMollifiedFComplex` and `selbergFourierLp_ae_eq_sqrt_mul_explicitKernel`.
- Produces: even Fourier norm-square energy and exact low/high substitutions under `y = 2*pi*w`.

- [ ] Write the failing contracts and verify RED.
- [ ] Prove `fourier F (-w) = conj (fourier F w)` for integrable real-valued complex `F`.
- [ ] Split the symmetric low/high sets into positive and negative halves, discarding only null endpoints.
- [ ] Prove the low Jacobian cancels `2*pi`, while the weighted high term gains exactly `4*pi^2`.
- [ ] Verify GREEN.

### Task 3: Genuine sliding-window S2 bound

**Files:**
- Create: `HardyTheorem/SelbergSlidingSecondMoment.lean`
- Create: `Test/SelbergSlidingSecondMomentContract.lean`
- Modify: `lakefile.lean`

**Interfaces:**
- Consumes: `MathlibAux.integral_normSq_slidingIntegral_le_fourier_low_high` and Tasks 1--2.
- Produces: the S2 second-moment bound for `selbergCompletedMollifiedFComplex` with `H = 2*pi / log(X^a)`.

- [ ] Write the failing contract and verify RED.
- [ ] Instantiate the genuine sliding-integral theorem.
- [ ] Substitute the exact low/high energy bounds.
- [ ] Use `L = a*log X` and absorb all fixed constants into one uniform witness.
- [ ] Run source, contract, target-build, placeholder, and diff checks.
- [ ] Commit, push, and update ready-for-review PR #484.
