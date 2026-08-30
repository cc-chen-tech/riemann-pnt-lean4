import PrimeNumberTheorem.MWKFCubicAFEDiagonalMellinIntegral

open PrimeNumberTheorem.MWKFCubic MeasureTheory
open scoped Interval

#check cubicAFECombinedSummandFinite_diagonalRay_eq_mellin
#check hasSum_intervalIntegral_cubicAFEDiagonalMellin
#check cubicAFEDiagonalMomentFinite_eq_mellin

-- Literal formula: no missing 2, 1/(2*pi), lcm or Mellin exponent.
example (W : CubicTestWeight) {T X : ℝ} (hT : T ≠ 0) (hX : 1 / 2 < X) (V : ℝ) :
    cubicAFEDiagonalMomentFinite W T X V =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∫ t : ℝ,
          ((cubicMollifierCoefficient T d : ℂ) * (cubicMollifierCoefficient T e : ℂ) * 2 *
            (W (t / T) : ℂ)) * (1 / (2 * Real.pi) : ℂ) *
          ∫ v : ℝ in -V..V, cubicAFEScalar t (cubicAFEVerticalPoint X v) *
            ((1 / (Nat.lcm d e : ℂ)) *
              (1 / (((d / Nat.gcd d e) * (e / Nat.gcd d e) : ℕ) : ℂ) ^ cubicAFEVerticalPoint X v) *
                riemannZeta (1 + 2 * cubicAFEVerticalPoint X v)) :=
  cubicAFEDiagonalMomentFinite_eq_mellin W hT hX V

-- Reversed vertical interval remains part of the exact identity.
example (t : ℝ) :
    HasSum (fun k : ℕ ↦ ∫ v : ℝ in (3 : ℝ)..(-3),
      cubicAFEScalar t (cubicAFEVerticalPoint 1 v) *
        cubicAFEDiagonalMellinMonomial 6 10 k (cubicAFEVerticalPoint 1 v))
      (∫ v : ℝ in (3 : ℝ)..(-3), cubicAFEDiagonalMellinKernel 6 10 t (cubicAFEVerticalPoint 1 v)) := by
  simpa only [neg_neg] using hasSum_intervalIntegral_cubicAFEDiagonalMellin
    t (by norm_num : 1 / 2 < (1 : ℝ)) (-3) (by norm_num : 0 < 6) (by norm_num : 0 < 10)
