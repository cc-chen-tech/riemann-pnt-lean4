/-
# Seed-deleted residual lemma: statement of record (and gap analysis)

This file records the precise mathematical statement of the
*seed-deleted residual lemma* that the sharp-constant transfer
(`ZeroDensityLayerBudgetSharpConstantTransfer.lean`) consumes as
its `c > 1/2` input.

It is intentionally a **statement of record**, not a proof.  The
companion document `docs/research/2026-08-17-seed-deleted-residual-analysis.md`
and the verification script `scripts/energy_verify.py` together
demonstrate that:

* The framework's `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
  produces a witness, but with coefficient `sqrt(D - B/L) ≈ 0.2`,
  which is **below** `1/2`.
* The lemma is therefore a **genuine mathematical gap**, not a Lean
  engineering task.

## Key finding (corrected)

The framework's machinery produces:
```
|cluster_main(x)| / amplitude ≥ sqrt(actualEqualRealPartZeroPackageEnergy)
                                       = sqrt(D - B/L)
                                       ≤ sqrt(D) ≈ 0.2
```

For the lemma to hold with `c > 1/2`, we need `sqrt(D - B/L) > 1/2`,
i.e., `D - B/L > 1/4 = 0.25`.  But `D` converges to ≈ 0.04 (NOT π²/6 ≈ 1.64)
as the package grows.  The framework's machinery is **insufficient**.

## How this file integrates

In a clean integration, the existing sharp-constant transfer would be
updated so that its only *required* hypothesis is the lemma below.
The lemma would then appear in the layer-budget tree as the single
external input that the entire transfer chain requires.

This is purely mechanical once the lemma is supplied.  Until then,
the lemma remains the single genuine mathematical gap in the chain.
-/

import Mathlib

open Complex Filter

namespace PrimeNumberTheorem

namespace SeedDeletedResidual

/-! ## Section 1: minimal terminology -/

/-- The relative Chebyshev ψ-error `(ψ(x) - x) / x`. -/
noncomputable def relativeChebyshevPsi0Error (x : ℝ) : ℝ :=
  (PrimeNumberTheorem.chebyshevPsi x - x) / x

/-- The target power amplitude `x ^ (beta - 1)`. -/
noncomputable def targetZeroPowerAmplitude (beta x : ℝ) : ℝ :=
  x ^ (beta - 1)

/-- Arbitrarily-far natural points where the absolute value of `f` is at
least `amplitude`.  This is the exact predicate consumed by the sharp
constant transfer. -/
def HasFarNaturalPointTargetAmplitudeWitness
    (f amplitude : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ amplitude m ≤ |f m|

/-- The cluster main term: a finite sum of relative zero contributions
coming from a chosen finite cluster `S`.  We define it in the *relative*
form (divided by `x`), matching `targetZeroPowerAmplitude = x^(beta - 1)`. -/
noncomputable def clusterMainTerm (S : Finset ℂ) (x : ℝ) : ℝ :=
  (∑ rho ∈ S,
      ((PrimeNumberTheorem.zeroMultiplicity rho : ℂ) *
          (x : ℂ) ^ (rho - 1) / (rho : ℂ))).re

/-! ## Section 2: the cluster-main witness input -/

/-- The cluster-main witness with coefficient `c`.  The sharp-constant
transfer takes this as its external input, asks `c > 1/2`, and produces
an outer Chebyshev witness with coefficient `c - 1/2 > 0`. -/
def ClusterMainWitness
    (beta c : ℝ) (S : Finset ℂ) : Prop :=
  c > 1 / 2 ∧
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ => clusterMainTerm S (m : ℝ))
      (fun m : ℕ => c * targetZeroPowerAmplitude beta (m : ℝ))

/-! ## Section 3: the equal-real-part package (key construction) -/

/-- The equal-real-part zeta-zero package: all nontrivial zeros with
`Re rho = beta` and `|Im rho| ≤ T`.  This is the natural finite-cluster
candidate for the seed-deleted residual lemma. -/
noncomputable def equalRealPartZeroPackage (T beta : ℝ) : Finset ℂ :=
  (PrimeNumberTheorem.nontrivialZerosFinset T).filter
    (fun rho => rho.re = beta)

/-- The diagonal energy of the package: `Σ m(ρ)² / |ρ|²`.  Under RH with
all multiplicities 1, this converges to ≈ 0.04 as `T → ∞`. -/
noncomputable def packageDiagonalEnergy (T beta : ℝ) : ℝ :=
  ∑ rho ∈ equalRealPartZeroPackage T beta,
    ‖(PrimeNumberTheorem.zeroMultiplicity rho : ℂ) * rho⁻¹‖ ^ 2

/-- The off-diagonal budget of the package.  Bounded above by
`Σ_{ρ ≠ ρ'} 2 · m(ρ) · m(ρ') / (|ρ| · |ρ'| · |Im ρ - Im ρ'|)`. -/
noncomputable def packageOffDiagonalBudget (T beta : ℝ) : ℝ :=
  PrimeNumberTheorem.ZeroForcedOscillation.offDiagonalBound
    (equalRealPartZeroPackage T beta)
    (fun rho => (PrimeNumberTheorem.zeroMultiplicity rho : ℂ) * rho⁻¹)
    Complex.im

/-- The mean-square energy of the package over a logarithmic interval
of length `L`. -/
noncomputable def packageMeanSquareEnergy (T beta L : ℝ) : ℝ :=
  packageDiagonalEnergy T beta - packageOffDiagonalBudget T beta / L

/-! ## Section 4: the seed-deleted residual lemma (statement of record) -/

/-- **Seed-deleted residual lemma** (precise statement).

This is the lemma that supplies the input hypothesis for the sharp
constant transfer.  It states:

> For every `lambda > 1`, there exists a *finite* cluster `S` of nontrivial
> zeta zeros, all lying on the line `Re rho = beta₀` for some fixed
> `beta₀ ∈ (1/2, 1)`, such that the cluster-main witness
> `ClusterMainWitness beta₀ c S` holds with `c > 1/2`. -/
def SeedDeletedResidualLemma
    (beta₀ lambda : ℝ) : Prop :=
  1 / 2 < beta₀ ∧
    1 < lambda ∧
    ∃ c : ℝ,
      1 / 2 < c ∧
      ∃ S : Finset ℂ,
        (∀ rho ∈ S,
          rho.re = beta₀ ∧ RiemannHypothesis.IsNontrivialZero rho) ∧
        ClusterMainWitness beta₀ c S

/-! ## Section 5: the gap

The lemma is **not provable** from existing framework machinery.

The framework's `hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`
delivers a witness with coefficient `sqrt(actualEqualRealPartZeroPackageEnergy)`,
which is bounded above by `sqrt(D) ≈ 0.2 < 1/2`.

To obtain `c > 1/2`, we would need a different kind of lower bound on
the cluster main term — one that captures constructive phase alignment.
This is not available in the framework or the literature.

## Status of the cluster-main witness input

The framework provides `ClusterMainWitness` (with `c ≈ 0.2`) but NOT
the version needed by the sharp transfer (`c > 1/2`).  The difference
is the genuine mathematical gap.

The accompanying Lean file documents the precise statement.  Closing
the gap requires either:

* A genuinely new result on the oscillation of the explicit formula
  (which is not in the literature), or
* Admitting the lemma as an external axiom and documenting its role.

## How this integrates

If admitted as an external input, the sharp-constant transfer would
take the lemma as its hypothesis, and all downstream consumers
(over 60 sites in the framework) would update symmetrically.  This
is purely mechanical work once the lemma is supplied.
-/

/-- **Theorem (witness placeholder).**

The eventual proof obligation: construct, for each admissible
`(beta₀, lambda)`, a coefficient `c > 1/2` and a finite cluster `S`
of zeta zeros on the line `Re rho = beta₀` such that the cluster-main
witness holds.

This theorem is currently *admitted* — it is the single external input
the framework requires.  A real proof requires new research. -/
theorem seedDeletedResidualLemmaWitness
    (beta₀ lambda : ℝ)
    (hbeta₀ : 1 / 2 < beta₀)
    (hlambda : 1 < lambda) :
    SeedDeletedResidualLemma beta₀ lambda := by
  -- ADMITTED.  This is the single gap in the chain.
  -- The proof requires new research and is not in the literature.
  sorry

/-! ## Section 6: framework's partial witness (insufficient) -/

/-- **Theorem (framework's partial witness).**

The framework provides a *partial* cluster-main witness via
`hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster`.  This
delivers coefficient `sqrt(actualEqualRealPartZeroPackageEnergy)`,
which is bounded above by `sqrt(D) ≈ 0.2 < 1/2`.

This theorem is **not** the seed-deleted residual lemma.  It is the
framework's best attempt; it falls short by a constant factor of
about 2.5×. -/
theorem framework_partial_witness
    (T beta L : ℝ)
    (hT : T > 0)
    (hbeta : 1 / 2 < beta)
    (hone : beta < 1)
    (hL : 0 < L)
    (H : ℝ → ℝ) (hH : Tendsto H atTop atTop) :
    HasFarNaturalPointTargetAmplitudeWitness
      (fun m : ℕ => clusterMainTerm (equalRealPartZeroPackage T beta) (m : ℝ))
      (fun m : ℕ =>
        Real.sqrt (packageMeanSquareEnergy T beta L) *
          targetZeroPowerAmplitude beta (m : ℝ)) := by
  -- This follows directly from the framework's
  -- hasFarTargetAmplitudeWitness_actualZeroPackage_visibleCluster
  -- combined with abs_dynamicVisibleClusterPNTMain_equalRealPartZeroPackage
  -- and the bridge dynamicVisibleClusterPNTZeroSum_equalRealPartZeroPackage.
  -- The coefficient is sqrt(actualEqualRealPartZeroPackageEnergy)
  -- = sqrt(packageMeanSquareEnergy).
  sorry

/-! ## Section 7: bridge to outer Chebyshev scale (mechanical) -/

/-- **Theorem (lemma implies outer Chebyshev witness).**

Once the lemma is supplied, the bridge to the outer Chebyshev scale
is exactly the sharp-constant transfer:
`actualWeightedBalancedGoodHeightPNTSharpConstantTransfer`.  The
framework already provides this transfer.  The proof below is
mechanical once the cluster-main witness is in place. -/
theorem SeedDeletedResidualLemma_implies_OuterChebyshevWitness
    {beta₀ lambda c : ℝ}
    (hseed : SeedDeletedResidualLemma beta₀ lambda)
    (hc : 1 / 2 < c)
    (_S : Finset ℂ) :
    ∃ q : ℝ, 0 < q ∧
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        (fun m : ℕ => q * targetZeroPowerAmplitude beta₀ (m : ℝ)) := by
  -- The bridge is the framework's `actualWeightedBalancedGoodHeightPNTSharpConstantTransfer`.
  sorry

end SeedDeletedResidual

end PrimeNumberTheorem