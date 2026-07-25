import PrimeNumberTheorem.VKEdgePiOverTwoCarlson

open Complex Filter Asymptotics

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

example (beta gamma : ℝ) (k : ℕ) :
    (oddHarmonicPoint beta gamma k).re = beta :=
  oddHarmonicPoint_re beta gamma k

example (beta gamma : ℝ) (k : ℕ) :
    (oddHarmonicPoint beta gamma k).im =
      ((2 * k + 1 : ℕ) : ℝ) * gamma :=
  oddHarmonicPoint_im beta gamma k

example {beta gamma sigma : ℝ} {M : ℕ}
    (hbeta0 : 0 < beta) (hbeta1 : beta < 1)
    (hgamma : 0 < gamma) (hsigma : sigma < beta)
    (hcount :
      ZeroDensity.zeroDensityCount sigma
          (((2 * M + 2 : ℕ) : ℝ) * gamma) ≤ M) :
    ∃ k : ℕ, k < M + 1 ∧
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 :=
  exists_riemannZeta_ne_zero_at_oddHarmonic_of_zeroDensityCount_le
    hbeta0 hbeta1 hgamma hsigma hcount

example {n : ℕ} (hn : 1 ≤ n) :
    0 < missingHarmonicDenominator n :=
  missingHarmonicDenominator_pos hn

example {n : ℕ} (hn : 1 ≤ n) :
    Real.pi / 2 < missingHarmonicLowerBound n :=
  pi_div_two_lt_missingHarmonicLowerBound hn

example (M : ℕ) :
    Real.pi / 2 < finiteOddHarmonicLowerBound M :=
  pi_div_two_lt_finiteOddHarmonicLowerBound M

example {sigma : ℝ} (hsigma : 1 / 2 < sigma) (hsigma1 : sigma < 1) :
    (fun T : ℝ => (ZeroDensity.zeroDensityCount sigma T : ℝ)) =o[atTop]
      (id : ℝ → ℝ) :=
  carlson_zeroDensity_isLittleO_id hsigma hsigma1

example {beta gamma sigma : ℝ}
    (hbeta1 : beta < 1) (hgamma : 0 < gamma)
    (hsigmaHalf : 1 / 2 < sigma) (hsigmaBeta : sigma < beta) :
    ∃ k : ℕ,
      riemannZeta (oddHarmonicPoint beta gamma k) ≠ 0 ∧
        Real.pi / 2 < missingHarmonicLowerBound (2 * k + 1) :=
  exists_missing_oddHarmonic_with_strict_gap_of_carlson
    hbeta1 hgamma hsigmaHalf hsigmaBeta

#print axioms
  exists_riemannZeta_ne_zero_at_oddHarmonic_of_zeroDensityCount_le
#print axioms pi_div_two_lt_missingHarmonicLowerBound
#print axioms pi_div_two_lt_finiteOddHarmonicLowerBound
#print axioms carlson_zeroDensity_isLittleO_id
#print axioms exists_missing_oddHarmonic_with_strict_gap_of_carlson

end VKEdgePiOverTwo
end PrimeNumberTheorem
