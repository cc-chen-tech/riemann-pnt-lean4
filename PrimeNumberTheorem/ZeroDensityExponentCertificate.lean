import PrimeNumberTheorem.CarlsonTwoThirdsDIExponent
import PrimeNumberTheorem.ZeroDensityCount

/-!
# Zero-density certificates with a free exponent

The record in this file packages an eventual pointwise majorant and converts
it to Mathlib's `IsBigO` relation.  It does not manufacture analytic input.
-/

namespace PrimeNumberTheorem

open Filter Asymptotics

/-- An eventual zero-density majorant with power exponent `q` and natural
logarithmic exponent `B`. -/
structure ZeroDensityEventualMajorant (σ q : ℝ) (B : ℕ) where
  C : ℝ
  C_nonneg : 0 ≤ C
  bound :
    ∀ᶠ T in atTop,
      (ZeroDensity.zeroDensityCount σ T : ℝ) ≤
        C * ‖T ^ q * (Real.log T) ^ B‖

namespace ZeroDensityEventualMajorant

/-- Convert an eventual pointwise certificate to the corresponding
`IsBigO` statement. -/
theorem isBigO {σ q : ℝ} {B : ℕ}
    (h : ZeroDensityEventualMajorant σ q B) :
    (fun T => (ZeroDensity.zeroDensityCount σ T : ℝ)) =O[atTop]
      (fun T => T ^ q * (Real.log T) ^ B) := by
  refine Asymptotics.IsBigO.of_bound h.C ?_
  filter_upwards [h.bound] with T hT
  have hcount_nonneg :
      0 ≤ (ZeroDensity.zeroDensityCount σ T : ℝ) := Nat.cast_nonneg _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hcount_nonneg] using hT

/-- Increasing the power exponent weakens an eventual density majorant. -/
def mono_exponent {σ q q' : ℝ} {B : ℕ}
    (h : ZeroDensityEventualMajorant σ q B) (hqq' : q ≤ q') :
    ZeroDensityEventualMajorant σ q' B := by
  refine ⟨h.C, h.C_nonneg, ?_⟩
  filter_upwards [h.bound, Filter.eventually_ge_atTop (1 : ℝ)] with T hbound hT
  have hT0 : 0 ≤ T := le_trans zero_le_one hT
  have hpow : T ^ q ≤ T ^ q' :=
    Real.rpow_le_rpow_of_exponent_le hT hqq'
  have hnormPow : ‖T ^ q‖ ≤ ‖T ^ q'‖ := by
    simpa only [Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hT0 q),
      abs_of_nonneg (Real.rpow_nonneg hT0 q')] using hpow
  have hmodel : ‖T ^ q * (Real.log T) ^ B‖ ≤
      ‖T ^ q' * (Real.log T) ^ B‖ := by
    simpa only [norm_mul] using
      mul_le_mul_of_nonneg_right hnormPow (norm_nonneg ((Real.log T) ^ B))
  exact hbound.trans (mul_le_mul_of_nonneg_left hmodel h.C_nonneg)

end ZeroDensityEventualMajorant

/-- The exact density certificate still required from the DI Carlson
local-to-global analysis.  This abbreviation is deliberately transparent:
no constructor is supplied by the exponent arithmetic alone. -/
abbrev CarlsonDIImprovedDensityCertificate : Type :=
  ZeroDensityEventualMajorant (2 / 3) diTargetExponent 6

namespace CarlsonDIImprovedDensityCertificate

/-- A populated DI density certificate gives the advertised improved
zero-density `IsBigO` statement. -/
theorem isBigO (h : CarlsonDIImprovedDensityCertificate) :
    (fun T => (ZeroDensity.zeroDensityCount (2 / 3) T : ℝ)) =O[atTop]
      (fun T => T ^ (467 / 576 : ℝ) * (Real.log T) ^ 6) := by
  simpa only [diTargetExponent] using
    (ZeroDensityEventualMajorant.isBigO h)

end CarlsonDIImprovedDensityCertificate

end PrimeNumberTheorem
