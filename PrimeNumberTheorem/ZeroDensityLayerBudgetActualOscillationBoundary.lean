import PrimeNumberTheorem.ZeroDensityLayerBudgetActualCarlsonCertificate
import PrimeNumberTheorem.ZeroForcingUnifiedTransfer

open Filter Topology

namespace PrimeNumberTheorem

/-!
# Boundary between actual Carlson tails and zero-forced oscillation

An actual Carlson certificate for the complete finite zero tail cannot be used
unchanged as the complementary-zero estimate in an oscillation proof: the
distinguished main cluster is itself part of that complete tail.  This module
records that obstruction and exposes the safe transfer interface, whose norm
majorant must already have the main cluster removed.
-/

/-- A signed remainder dominated by an eventually negligible nonnegative
majorant is negligible on the same target-amplitude scale. -/
theorem TargetAmplitudeNegligible.of_eventually_abs_le
    {amplitude remainder majorant : ℝ → ℝ}
    (hamplitude : ∀ᶠ x in atTop, 0 < amplitude x)
    (hmajorant : TargetAmplitudeNegligible amplitude majorant)
    (hdominated : ∀ᶠ x in atTop, |remainder x| ≤ majorant x) :
    TargetAmplitudeNegligible amplitude remainder := by
  unfold TargetAmplitudeNegligible at hmajorant ⊢
  refine squeeze_zero' ?_ ?_ hmajorant
  · filter_upwards [hamplitude] with x hx
    exact div_nonneg (abs_nonneg _) (le_of_lt hx)
  · filter_upwards [hamplitude, hdominated] with x hx hdominatedX
    exact
      div_le_div_of_nonneg_right
        (hdominatedX.trans (le_abs_self (majorant x))) (le_of_lt hx)

/--
Misuse guard for the complete actual zero tail.

If a main term is pointwise dominated by the complete tail certified by
Carlson, that complete tail cannot simultaneously be negligible relative to
the target amplitude and support a far target-amplitude main-term witness.
Consequently the complete-tail certificate must not be substituted for a
cluster-excluded complementary-zero certificate.
-/
theorem ActualCarlsonFiniteStripCertificate.not_fullTail_dominates_farWitness
    {beta alpha : ℝ} {n : ℕ}
    {input :
      (x : ℝ) →
        PositiveZeroBucketInput (carlsonPolynomialHeight alpha x) n}
    (certificate : ActualCarlsonFiniteStripCertificate beta alpha n input)
    {main : ℝ → ℝ}
    (hdominated :
      ∀ x,
        |main x| ≤
          dynamicFullPNTZeroTailNorm (carlsonPolynomialHeight alpha) x) :
    ¬ HasFarTargetAmplitudeWitness main
        (targetZeroPowerAmplitude beta) := by
  intro hmain
  have hsmall :=
    eventually_abs_lt_mul_of_targetAmplitudeNegligible
      (targetZeroPowerAmplitude_eventually_pos beta)
      certificate.fullTail_negligible (epsilon := (1 : ℝ)) zero_lt_one
  rw [eventually_atTop] at hsmall
  rcases hsmall with ⟨X₀, hsmall⟩
  rcases hmain X₀ with ⟨x, hx, hmainX⟩
  have hcontra :
      targetZeroPowerAmplitude beta x <
        targetZeroPowerAmplitude beta x := by
    calc
      targetZeroPowerAmplitude beta x ≤ |main x| := hmainX
      _ ≤ dynamicFullPNTZeroTailNorm
          (carlsonPolynomialHeight alpha) x := hdominated x
      _ ≤ |dynamicFullPNTZeroTailNorm
          (carlsonPolynomialHeight alpha) x| := le_abs_self _
      _ < 1 * targetZeroPowerAmplitude beta x := hsmall x hx
      _ = targetZeroPowerAmplitude beta x := one_mul _
  exact (lt_irrefl _ hcontra)

/--
The safe normalized certificate for a signed complementary-zero term.

`excludedTailNorm` is required to represent a zero-tail norm after removal of
the distinguished finite main cluster.  The structure deliberately does not
offer a constructor from `ActualCarlsonFiniteStripCertificate`: constructing
the cluster-excluded Carlson partition is the remaining analytic bridge.
-/
structure ClusterExcludedTargetComplementCertificate
    (amplitude complement excludedTailNorm : ℝ → ℝ) : Prop where
  amplitude_eventually_pos :
    ∀ᶠ x in atTop, 0 < amplitude x
  complement_dominated :
    ∀ᶠ x in atTop, |complement x| ≤ excludedTailNorm x
  excluded_tail_negligible :
    TargetAmplitudeNegligible amplitude excludedTailNorm

/-- A cluster-excluded norm certificate supplies the signed complementary
hypothesis expected by the target-amplitude transfer machine. -/
theorem ClusterExcludedTargetComplementCertificate.complement_negligible
    {amplitude complement excludedTailNorm : ℝ → ℝ}
    (certificate :
      ClusterExcludedTargetComplementCertificate
        amplitude complement excludedTailNorm) :
    TargetAmplitudeNegligible amplitude complement :=
  certificate.excluded_tail_negligible.of_eventually_abs_le
    certificate.amplitude_eventually_pos certificate.complement_dominated

/--
Safe upper/lower PNT transfer with a cluster-excluded complementary-zero
certificate.

The parametric Pintz--Carlson upper theorem and the finite-cluster lower
transfer act on the same `relativeChebyshevPsi0Error`.  Unlike the older
interface, the signed complement hypothesis is discharged by a norm majorant
that explicitly excludes the distinguished cluster.
-/
theorem unified_parametricPNTUpper_clusterExcludedComplementLower
    (threshold : ℝ) (hhalf : 1 / 2 < threshold) (hlt : threshold < 1)
    {amplitude main realAxis contour complement excludedTailNorm : ℝ → ℝ}
    (certificate :
      ClusterExcludedTargetComplementCertificate
        amplitude complement excludedTailNorm)
    (hrealAxis : TargetAmplitudeNegligible amplitude realAxis)
    (hcontour : TargetAmplitudeNegligible amplitude contour)
    (hmain : HasFarTargetAmplitudeWitness main amplitude)
    (hdecomp :
      ∀ x : ℝ,
        relativeChebyshevPsi0Error x =
          main x + (realAxis x + contour x + complement x)) :
    (∃ rate : ℝ, 0 < rate ∧ rate ≤ 1 ∧
      Tendsto
        (fun m : ℕ => relativeChebyshevPsi0Error (m : ℝ))
        atTop (nhds 0)) ∧
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => amplitude x / 2) := by
  exact
    unified_parametricPNTUpper_targetAmplitudeLower
      threshold hhalf hlt certificate.amplitude_eventually_pos
      hrealAxis hcontour certificate.complement_negligible hmain hdecomp

end PrimeNumberTheorem
