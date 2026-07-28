import MathlibAux.DriftingExponentialPolynomialHilbert
import PrimeNumberTheorem.VKEdgeZeroClusterPhaseCoercivity

open Complex MeasureTheory Set
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Local second-moment coercivity for finite zeta-zero clusters

This module combines the collision-safe drifting model, the concrete
Carneiro--Littmann local-separation Hilbert bound, and phase coercivity for
equal positive ordinates.  Every unresolved near-frequency interaction
remains visible in `finiteZeroClusterLocalSeparationEnergy`.
-/

/-- Total norm mass of the frozen multiplicity-weighted zero coefficients. -/
noncomputable def finiteZeroClusterCoefficientMass
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (beta a : ℝ) : ℝ :=
  ∑ rho ∈ S,
    ‖finiteZeroClusterCoefficientAt multiplicity beta a rho‖

/-- Diagonal energy after coefficients with equal ordinates are merged. -/
noncomputable def finiteZeroClusterMergedEnergy
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (beta a : ℝ) : ℝ :=
  ∑ gamma ∈ MathlibAux.mergedFrequencySupport S Complex.im,
    ‖MathlibAux.mergedFrequencyCoefficient S
        (finiteZeroClusterCoefficientAt multiplicity beta a)
        Complex.im gamma‖ ^ 2

/-- The merged coefficient energy weighted by reciprocal local ordinate
separation.  This is the spectral loss in the Hilbert lower bound. -/
noncomputable def finiteZeroClusterLocalSeparationEnergy
    (S : Finset ℂ) (multiplicity : ℂ → ℕ)
    (beta a : ℝ) : ℝ :=
  MathlibAux.exponentialPolynomialLocalSeparationEnergy
    (MathlibAux.mergedFrequencySupport S Complex.im)
    (MathlibAux.mergedFrequencyCoefficient S
      (finiteZeroClusterCoefficientAt multiplicity beta a) Complex.im)
    id

private theorem finiteZeroCluster_drift_mem_localL2
    {S : Finset ℂ} {beta delta : ℝ}
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta) :
    ∀ rho ∈ S,
      -delta ≤ rho.re - beta ∧ rho.re - beta ≤ 0 := by
  intro rho hrho
  have h := hband rho hrho
  constructor <;> linarith

/-- Local `L2` lower bound for a finite normalized zeta-zero cluster. Equal
ordinates are merged, and all remaining near-frequency interaction is charged
to the explicit local-separation energy. -/
theorem
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_localSeparation
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 2 : ℝ) *
          (L * finiteZeroClusterMergedEnergy S multiplicity beta a -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy
                S multiplicity beta a) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 := by
  have hbase :=
    MathlibAux.integral_normSq_driftingExponentialPolynomial_ge_merged_localSeparation
      (S := S)
      (coeff := finiteZeroClusterCoefficientAt multiplicity beta a)
      (freq := Complex.im)
      (drift := fun rho => rho.re - beta)
      (a := a) (L := L) (delta := delta)
      hL hdelta (finiteZeroCluster_drift_mem_localL2 hband) hsupport
  have hrewrite :
      (∫ y in a..(a + L),
          ‖MathlibAux.driftingExponentialPolynomial S
            (finiteZeroClusterCoefficientAt multiplicity beta a)
            Complex.im (fun rho => rho.re - beta) a y‖ ^ 2) =
        ∫ y in a..(a + L),
          ‖normalizedFiniteZeroClusterContribution
            S multiplicity beta y‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro y hy
    exact congrArg (fun z : ℂ => ‖z‖ ^ 2)
      (normalizedFiniteZeroClusterContribution_eq_drifting
        S multiplicity beta a y).symm
  simpa [finiteZeroClusterMergedEnergy,
    finiteZeroClusterLocalSeparationEnergy,
    finiteZeroClusterCoefficientMass, hrewrite] using hbase

/-- Phase coercivity converts merged diagonal energy into a lower bound in
terms of the full coefficient mass, losing only four times the number of
distinct ordinates. -/
theorem
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_phaseCoercive_localSeparation
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial) :
    (1 / 2 : ℝ) *
          (L /
                (4 *
                  (MathlibAux.mergedFrequencySupport S Complex.im).card) *
              finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 -
            4 * Real.pi *
              finiteZeroClusterLocalSeparationEnergy
                S multiplicity beta a) -
        L * (1 - Real.exp (-delta * L)) ^ 2 *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 := by
  let U : Finset ℝ := MathlibAux.mergedFrequencySupport S Complex.im
  let mass : ℝ := finiteZeroClusterCoefficientMass S multiplicity beta a
  let energy : ℝ := finiteZeroClusterMergedEnergy S multiplicity beta a
  let spectral : ℝ :=
    finiteZeroClusterLocalSeparationEnergy S multiplicity beta a
  let q : ℝ := 1 - Real.exp (-delta * L)
  have hbase :=
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_localSeparation
      (S := S) (multiplicity := multiplicity)
      (beta := beta) (a := a) (L := L) (delta := delta)
      hL hdelta hband hsupport
  have hphase :=
    totalCoefficientMass_sq_le_four_card_mul_mergedFrequencyEnergy
      (S := S) (multiplicity := multiplicity)
      (beta := beta) (a := a) hre him
  have hcardNat : 0 < U.card := hsupport.nonempty.card_pos
  have hdenom : 0 < (4 * (U.card : ℝ)) := by positivity
  have hphase' :
      mass ^ 2 ≤ 4 * (U.card : ℝ) * energy := by
    simpa [U, mass, energy, finiteZeroClusterCoefficientMass,
      finiteZeroClusterMergedEnergy] using hphase
  have henergy :
      mass ^ 2 / (4 * (U.card : ℝ)) ≤ energy :=
    (div_le_iff₀ hdenom).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hphase')
  have hscaled :
      L / (4 * (U.card : ℝ)) * mass ^ 2 ≤ L * energy := by
    calc
      L / (4 * (U.card : ℝ)) * mass ^ 2 =
          L * (mass ^ 2 / (4 * (U.card : ℝ))) := by ring
      _ ≤ L * energy := mul_le_mul_of_nonneg_left henergy hL
  change
    (1 / 2 : ℝ) *
          (L / (4 * (U.card : ℝ)) * mass ^ 2 -
            4 * Real.pi * spectral) -
        L * q ^ 2 * mass ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2
  change
    (1 / 2 : ℝ) * (L * energy - 4 * Real.pi * spectral) -
        L * q ^ 2 * mass ^ 2 ≤
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 at hbase
  exact
    (by
      have :
          (1 / 2 : ℝ) *
                (L / (4 * (U.card : ℝ)) * mass ^ 2 -
                  4 * Real.pi * spectral) -
              L * q ^ 2 * mass ^ 2 ≤
            (1 / 2 : ℝ) * (L * energy - 4 * Real.pi * spectral) -
              L * q ^ 2 * mass ^ 2 := by
        linarith
      exact this.trans hbase)

/-- Explicit coercivity gate: if the phase-protected diagonal mass dominates
the local-separation Hilbert loss and twice the drift loss, then the finite
normalized zero cluster has strictly positive local second moment. -/
theorem
    integral_normSq_normalizedFiniteZeroClusterContribution_pos_of_localSeparation
    {S : Finset ℂ} {multiplicity : ℂ → ℕ}
    {beta a L delta : ℝ}
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ rho ∈ S, beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hre : ∀ rho ∈ S, 0 < rho.re ∧ rho.re ≤ 1)
    (him : ∀ rho ∈ S, 1 ≤ rho.im)
    (hsupport : (MathlibAux.mergedFrequencySupport S Complex.im).Nontrivial)
    (hcoercive :
      4 * Real.pi *
            finiteZeroClusterLocalSeparationEnergy
              S multiplicity beta a +
          2 * L * (1 - Real.exp (-delta * L)) ^ 2 *
            finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2 <
        L /
            (4 * (MathlibAux.mergedFrequencySupport S Complex.im).card) *
          finiteZeroClusterCoefficientMass S multiplicity beta a ^ 2) :
    0 <
      ∫ y in a..(a + L),
        ‖normalizedFiniteZeroClusterContribution
          S multiplicity beta y‖ ^ 2 := by
  have hbase :=
    integral_normSq_normalizedFiniteZeroClusterContribution_ge_phaseCoercive_localSeparation
      (S := S) (multiplicity := multiplicity)
      (beta := beta) (a := a) (L := L) (delta := delta)
      hL hdelta hband hre him hsupport
  linarith

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
