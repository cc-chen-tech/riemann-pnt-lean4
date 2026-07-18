import ZeroFreeRegion.VinogradovKorobov.VanDerCorput
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Analysis.Complex.Trigonometric

open Complex
open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

/-- A unit complex exponential attached to a real phase on the integers. -/
noncomputable def phaseTerm (f : ℕ → ℝ) (n : ℕ) : ℂ :=
  Complex.exp (I * (f n : ℂ))

lemma norm_phaseTerm (f : ℕ → ℝ) (n : ℕ) :
    ‖phaseTerm f n‖ = 1 := by
  simp [phaseTerm, Complex.norm_exp]

/-- Autocorrelation of unit phases is the exponential of the phase
difference.  This is the form consumed by van der Corput differencing. -/
lemma phaseTerm_mul_conj_shift (f : ℕ → ℝ) (n h : ℕ) :
    phaseTerm f n * (starRingEnd ℂ) (phaseTerm f (n + h)) =
      Complex.exp (I * ((f n - f (n + h) : ℝ) : ℂ)) := by
  change Complex.exp (I * (f n : ℂ)) *
      star (Complex.exp (I * (f (n + h) : ℂ))) = _
  rw [show star (Complex.exp (I * (f (n + h) : ℂ))) =
      Complex.exp (star (I * (f (n + h) : ℂ))) by
        simpa using
          (Complex.exp_conj (I * (f (n + h) : ℂ))).symm]
  rw [← Complex.exp_add]
  congr 1
  simp
  ring

/-- The length-`N` exponential sum with linear increment `theta`. -/
noncomputable def linearPhaseSum (theta : ℝ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.range N,
    Complex.exp ((n : ℂ) * (I * (theta : ℂ)))

lemma linearPhaseSum_eq_geom (theta : ℝ) (N : ℕ) :
    linearPhaseSum theta N =
      ∑ n ∈ Finset.range N, (Complex.exp (I * (theta : ℂ))) ^ n := by
  apply Finset.sum_congr rfl
  intro n hn
  exact Complex.exp_nat_mul (I * (theta : ℂ)) n

/-- The trivial estimate for a linear phase sum. -/
theorem norm_linearPhaseSum_le_length (theta : ℝ) (N : ℕ) :
    ‖linearPhaseSum theta N‖ ≤ N := by
  unfold linearPhaseSum
  calc
    ‖∑ n ∈ Finset.range N,
        Complex.exp ((n : ℂ) * (I * (theta : ℂ)))‖
        ≤ ∑ n ∈ Finset.range N,
            ‖Complex.exp ((n : ℂ) * (I * (theta : ℂ)))‖ :=
      norm_sum_le _ _
    _ = N := by simp [Complex.norm_exp]

/-- Geometric cancellation for a nonconstant linear phase. -/
theorem norm_linearPhaseSum_le_two_div (theta : ℝ) (N : ℕ)
    (htheta : Complex.exp (I * (theta : ℂ)) ≠ 1) :
    ‖linearPhaseSum theta N‖ ≤
      2 / ‖Complex.exp (I * (theta : ℂ)) - 1‖ := by
  let q : ℂ := Complex.exp (I * (theta : ℂ))
  have hq : q ≠ 1 := htheta
  have hqnorm : ‖q‖ = 1 := by
    simp [q, Complex.norm_exp]
  have hden : 0 < ‖q - 1‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hq)
  rw [linearPhaseSum_eq_geom, geom_sum_eq hq N, norm_div]
  apply (div_le_div_iff_of_pos_right hden).2
  calc
    ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by rw [norm_pow, hqnorm]; norm_num

/-- The useful linear-phase bound is the minimum of cancellation and the
trivial length estimate. -/
theorem norm_linearPhaseSum_le_min (theta : ℝ) (N : ℕ)
    (htheta : Complex.exp (I * (theta : ℂ)) ≠ 1) :
    ‖linearPhaseSum theta N‖ ≤
      min (N : ℝ) (2 / ‖Complex.exp (I * (theta : ℂ)) - 1‖) := by
  exact le_min
    (norm_linearPhaseSum_le_length theta N)
    (norm_linearPhaseSum_le_two_div theta N htheta)

end ZeroFreeRegion.VinogradovKorobov
