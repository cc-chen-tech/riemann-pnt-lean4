import PrimeNumberTheorem.RieszDifference
import PrimeNumberTheorem.SecondOrderMovingLeft
import PrimeNumberTheorem.RightHorizontalEdge
import PrimeNumberTheorem.CentralHorizontalEdge
import PrimeNumberTheorem.LeftVerticalEdge
import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.FirstOrderExplicitFormula
import PrimeNumberTheorem.ZetaDerivativeZero

/-!
# Transferring smoothed approximation errors to Chebyshev psi

This module isolates the algebraic step needed after a finite-height
second-order explicit formula supplies approximations to the first Riesz mean.
In particular, callers can use the residue sum minus contour remainder from
`SecondOrderExplicitFormula` as `approx`. The approximation and its error may
both depend on the height parameter `T`.
-/

open Complex
open scoped BigOperators Interval

namespace PrimeNumberTheorem

namespace ExplicitFormulaResidues

/-- Difference, in the `x` variable, of one horizontal second-order contour
edge. -/
noncomputable def secondOrderHorizontalXDifference
    (x y a c T : ℝ) : ℂ :=
  (∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + T * I)) -
    ∫ σ : ℝ in a..c,
      secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + T * I)

/-- Difference, in the `x` variable, of the left vertical second-order edge. -/
noncomputable def secondOrderLeftXDifference
    (x y a W : ℝ) : ℂ :=
  (∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      secondOrderExplicitFormulaIntegrand y ((a : ℂ) + t * I)) -
    ∫ t : ℝ in (-(2 * Real.pi * W))..(2 * Real.pi * W),
      secondOrderExplicitFormulaIntegrand x ((a : ℂ) + t * I)

/-- The negative-odd left-vertical majorant for the second-order Perron
kernel.  Relative to the first-order API, the extra kernel contributes the
explicit factor `(2N+1)^{-1}`. -/
noncomputable def secondOrderOddVerticalBound (x : ℝ) (N : ℕ) (T : ℝ) : ℝ :=
  (vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (2 * (N : ℝ) + T + 4)) + Real.pi) *
      x ^ (-(2 * (N : ℝ) + 1)) / (2 * (N : ℝ) + 1)

/-- On a finite negative-odd vertical segment, the second-order Perron kernel
gains the reciprocal distance of the line from the imaginary axis.  Positivity
of `x` is sufficient, including the endpoint `x = 1` used by the smoothed
transfer theorem. -/
theorem norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
    {x T t : ℝ} {N : ℕ} (hx : 0 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      secondOrderOddVerticalBound x N T := by
  let s : ℂ := ((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  have hlog := norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
    (N := N) hT ht
  change ‖-logDeriv riemannZeta s‖ ≤ Q at hlog
  have hpow : ‖(x : ℂ) ^ s‖ = x ^ (-(2 * (N : ℝ) + 1)) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx]
    simp [s]
  have hline_one : 1 ≤ ‖s‖ := by
    have hre : 2 * (N : ℝ) + 1 ≤ |s.re| := by
      simp [s]
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      rw [abs_of_nonpos (by linarith)]
      linarith
    have habs := Complex.abs_re_le_norm s
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  change ‖explicitFormulaIntegrand x s / s‖ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) /
    (2 * (N : ℝ) + 1)
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hden_pos : 0 < 2 * (N : ℝ) + 1 := by linarith
  have hden : 2 * (N : ℝ) + 1 ≤ ‖s‖ := by
    have hre : 2 * (N : ℝ) + 1 ≤ |s.re| := by
      simp [s]
      rw [abs_of_nonpos (by linarith)]
      linarith
    exact hre.trans (Complex.abs_re_le_norm s)
  have hQ : 0 ≤ Q := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hM : 1 ≤ 2 * (N : ℝ) + T + 4 := by linarith
    have hlog : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) := Real.log_nonneg hM
    dsimp [Q]
    positivity
  have hnum : 0 ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
    mul_nonneg hQ (Real.rpow_nonneg hx.le _)
  have hfirst :
      ‖explicitFormulaIntegrand x s‖ ≤
        Q * x ^ (-(2 * (N : ℝ) + 1)) := by
    simp only [explicitFormulaIntegrand]
    rw [norm_div, norm_mul, hpow]
    calc
      ‖-logDeriv riemannZeta s‖ * x ^ (-(2 * (N : ℝ) + 1)) / ‖s‖ ≤
          (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ := by
        gcongr
      _ ≤ Q * x ^ (-(2 * (N : ℝ) + 1)) :=
        div_le_self hnum hline_one
  rw [norm_div]
  calc
    ‖explicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (Q * x ^ (-(2 * (N : ℝ) + 1))) / ‖s‖ :=
      div_le_div_of_nonneg_right hfirst (norm_nonneg s)
    _ ≤ (Q * x ^ (-(2 * (N : ℝ) + 1))) / (2 * (N : ℝ) + 1) :=
      div_le_div_of_nonneg_left hnum hden_pos hden

/-- Compatibility form of
`norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos` with the
historical `1 < x` hypothesis. -/
theorem norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le
    {x T t : ℝ} {N : ℕ} (hx : 1 < x) (hT : 0 ≤ T) (ht : |t| ≤ T) :
    ‖secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      secondOrderOddVerticalBound x N T :=
  norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
    (zero_lt_one.trans hx) hT ht

/-- Quantitative endpoint-difference bound for the second-order left vertical
edge on the negative-odd line `Re(s)=-(2N+1)`.  The only restriction on the
height parameter is nonnegativity; no good-height hypothesis is used here. -/
theorem norm_secondOrderLeftXDifference_odd_le_of_pos
    {x y W : ℝ} {N : ℕ} (hx : 0 < x) (hy : 0 < y) (hW : 0 ≤ W) :
    ‖secondOrderLeftXDifference x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (secondOrderOddVerticalBound y N (2 * Real.pi * W) +
        secondOrderOddVerticalBound x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) := by
  let T : ℝ := 2 * Real.pi * W
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hyIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => secondOrderExplicitFormulaIntegrand y
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := secondOrderOddVerticalBound y N T)
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
        hy hT habs)
  have hxIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ => secondOrderExplicitFormulaIntegrand x
      (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := secondOrderOddVerticalBound x N T)
    (fun t ht => by
      rw [Set.uIoc_of_le (by linarith)] at ht
      have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
      exact norm_secondOrderExplicitFormulaIntegrand_odd_vertical_le_of_pos
        hx hT habs)
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hyIntegral hxIntegral
  unfold secondOrderLeftXDifference
  change ‖(∫ t : ℝ in (-T)..T,
      secondOrderExplicitFormulaIntegrand y
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)) -
      ∫ t : ℝ in (-T)..T,
        secondOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
  calc
    _ ≤ ‖∫ t : ℝ in (-T)..T,
          secondOrderExplicitFormulaIntegrand y
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ +
        ‖∫ t : ℝ in (-T)..T,
          secondOrderExplicitFormulaIntegrand x
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ :=
      norm_sub_le _ _
    _ ≤ secondOrderOddVerticalBound y N T * (T - -T) +
        secondOrderOddVerticalBound x N T * (T - -T) :=
      add_le_add hyIntegral hxIntegral
    _ = _ := by dsimp [T]; ring

/-- Compatibility form of `norm_secondOrderLeftXDifference_odd_le_of_pos`
with the historical strict endpoint hypotheses. -/
theorem norm_secondOrderLeftXDifference_odd_le
    {x y W : ℝ} {N : ℕ} (hx : 1 < x) (hy : 1 < y) (hW : 0 ≤ W) :
    ‖secondOrderLeftXDifference x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (secondOrderOddVerticalBound y N (2 * Real.pi * W) +
        secondOrderOddVerticalBound x N (2 * Real.pi * W)) *
        (2 * (2 * Real.pi * W)) :=
  norm_secondOrderLeftXDifference_odd_le_of_pos
    (zero_lt_one.trans hx) (zero_lt_one.trans hy) hW

/-- Pointwise endpoint cancellation on a negative-odd left vertical line.
The second-order kernel spends one factor of `s` on the endpoint exponential
difference, leaving the explicit logarithmic gap. -/
theorem
    norm_secondOrderExplicitFormulaIntegrand_sub_odd_vertical_le_of_pos
    {x y T t : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y)
    (hT : 0 ≤ T) (ht : |t| ≤ T)
    (hsmall :
      (2 * (N : ℝ) + 1 + T) * (Real.log y - Real.log x) ≤ 1) :
    ‖secondOrderExplicitFormulaIntegrand y
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) -
        secondOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤
      2 * secondOrderOddVerticalBound x N T *
        (Real.log y - Real.log x) := by
  let m : ℝ := 2 * (N : ℝ) + 1
  let s : ℂ := ((-m : ℝ) : ℂ) + (t : ℂ) * I
  let d : ℝ := Real.log y - Real.log x
  let Q : ℝ := vonMangoldtLSeriesNorm 1 + ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
      Real.log (2 * (N : ℝ) + T + 4)) + Real.pi
  have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
  have hmpos : 0 < m := by dsimp [m]; linarith
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s, m] at hre
    linarith
  have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hd : 0 ≤ d := by
    dsimp [d]
    exact sub_nonneg.mpr (Real.log_le_log hx hxy)
  have hsNormUpper : ‖s‖ ≤ m + T := by
    calc
      ‖s‖ ≤ ‖((-m : ℝ) : ℂ)‖ + ‖(t : ℂ) * I‖ := by
        exact norm_add_le _ _
      _ = m + |t| := by
        rw [norm_mul, norm_I, mul_one, Complex.norm_real,
          Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_neg, abs_of_pos hmpos]
      _ ≤ m + T := by linarith
  have hsmallNorm : ‖s‖ * d ≤ 1 := by
    calc
      ‖s‖ * d ≤ (m + T) * d :=
        mul_le_mul_of_nonneg_right hsNormUpper hd
      _ ≤ 1 := by simpa [m, d] using hsmall
  have hfac :
      (y : ℂ) ^ s - (x : ℂ) ^ s =
        (x : ℂ) ^ s * (Complex.exp ((d : ℂ) * s) - 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [← Complex.ofReal_log hy.le, ← Complex.ofReal_log hx.le]
    rw [show (Real.log y : ℂ) * s =
        (Real.log x : ℂ) * s + (d : ℂ) * s by
          simp only [d, Complex.ofReal_sub]
          ring]
    rw [Complex.exp_add]
    ring
  have hzNorm : ‖(d : ℂ) * s‖ = d * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  have hzSmall : ‖(d : ℂ) * s‖ ≤ 1 := by
    rw [hzNorm, mul_comm]
    exact hsmallNorm
  have hrem : ‖Complex.exp ((d : ℂ) * s) - 1‖ ≤ 2 * (d * ‖s‖) := by
    simpa [abs_of_nonneg hd] using Complex.norm_exp_sub_one_le hzSmall
  have hsre : s.re = -m := by simp [s]
  have hpow : ‖(x : ℂ) ^ s‖ = x ^ (-m) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos hx, hsre]
  have hfactor :
      ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
        2 * x ^ (-m) * d / ‖s‖ := by
    rw [hfac, norm_div, norm_mul, norm_pow, hpow]
    calc
      x ^ (-m) * ‖Complex.exp ((d : ℂ) * s) - 1‖ / ‖s‖ ^ 2 ≤
          x ^ (-m) * (2 * (d * ‖s‖)) / ‖s‖ ^ 2 := by
        gcongr
      _ = 2 * x ^ (-m) * d / ‖s‖ := by
        field_simp [ne_of_gt hsNormPos]
  have hline : m ≤ ‖s‖ := by
    have hre : m ≤ |s.re| := by
      rw [hsre, abs_neg, abs_of_pos hmpos]
    exact hre.trans (Complex.abs_re_le_norm s)
  have hlog := norm_neg_logDeriv_riemannZeta_odd_vertical_le_of_abs_le
    (N := N) hT ht
  change ‖-logDeriv riemannZeta s‖ ≤ Q at hlog
  have hQ : 0 ≤ Q := by
    have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    have hM : 1 ≤ 2 * (N : ℝ) + T + 4 := by linarith
    have hlogM : 0 ≤ Real.log (2 * (N : ℝ) + T + 4) :=
      Real.log_nonneg hM
    dsimp [Q]
    positivity
  have hrewrite :
      secondOrderExplicitFormulaIntegrand y s -
          secondOrderExplicitFormulaIntegrand x s =
        -logDeriv riemannZeta s *
          (((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2) := by
    unfold secondOrderExplicitFormulaIntegrand explicitFormulaIntegrand
    ring
  change ‖secondOrderExplicitFormulaIntegrand y s -
      secondOrderExplicitFormulaIntegrand x s‖ ≤ _
  rw [hrewrite, norm_mul]
  calc
    ‖-logDeriv riemannZeta s‖ *
          ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
        Q * (2 * x ^ (-m) * d / ‖s‖) :=
      mul_le_mul hlog hfactor (norm_nonneg _) hQ
    _ ≤ Q * (2 * x ^ (-m) * d / m) := by
      gcongr
    _ = 2 * secondOrderOddVerticalBound x N T *
          (Real.log y - Real.log x) := by
      unfold secondOrderOddVerticalBound
      dsimp [Q, m, d]
      ring

/-- The second-order explicit-formula integrand is interval integrable on
every finite negative-odd vertical segment for every positive endpoint. -/
theorem
    intervalIntegrable_secondOrderExplicitFormulaIntegrand_odd_vertical_of_pos
    {x T : ℝ} {N : ℕ} (hx : 0 < x) :
    IntervalIntegrable
      (fun t : ℝ => secondOrderExplicitFormulaIntegrand x
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
      MeasureTheory.volume (-T) T := by
  apply ContinuousOn.intervalIntegrable
  intro t _ht
  let s : ℂ :=
    (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)
  have hs0 : s ≠ 0 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hs1 : s ≠ 1 := by
    intro hs
    have hre := congrArg Complex.re hs
    simp [s] at hre
    have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1) := by
    intro n hn
    have hre := congrArg Complex.re hn
    simp [s] at hre
    have heqR : 2 * (N : ℝ) + 1 = 2 * ((n : ℝ) + 1) := by
      linarith
    have hparity : 2 * N + 1 = 2 * (n + 1) := by
      exact_mod_cast heqR
    omega
  have hzeta : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_re_le_zero
      (by
        simp [s]
        have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith)
      htrivial
  have hanalytic :
      AnalyticAt ℂ (secondOrderExplicitFormulaIntegrand x) s := by
    simpa [secondOrderExplicitFormulaIntegrand] using
      (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
          hx hs0 hs1 hzeta).div analyticAt_id hs0
  have hmap :
      ContinuousAt
        (fun r : ℝ =>
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (r : ℂ) * I)) t := by
    fun_prop
  simpa [s, Function.comp_def] using
    (hanalytic.continuousAt.comp_of_eq hmap (by simp [s])).continuousWithinAt

/-- The left-vertical endpoint difference is bounded after subtracting the
two endpoint kernels before integration.  In contrast to the separate
endpoint estimate, the bound contains the explicit logarithmic gap. -/
theorem norm_secondOrderLeftXDifference_odd_increment_le_of_pos
    {x y W : ℝ} {N : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hxy : x ≤ y) (hW : 0 ≤ W)
    (hsmall :
      (2 * (N : ℝ) + 1 + 2 * Real.pi * W) *
        (Real.log y - Real.log x) ≤ 1) :
    ‖secondOrderLeftXDifference x y (-(2 * (N : ℝ) + 1)) W‖ ≤
      (2 * secondOrderOddVerticalBound x N (2 * Real.pi * W) *
          (Real.log y - Real.log x)) *
        (2 * (2 * Real.pi * W)) := by
  let T : ℝ := 2 * Real.pi * W
  let K : ℝ :=
    2 * secondOrderOddVerticalBound x N T *
      (Real.log y - Real.log x)
  have hT : 0 ≤ T := by
    dsimp [T]
    positivity
  have hpoint : ∀ t ∈ Set.uIoc (-T) T,
      ‖secondOrderExplicitFormulaIntegrand y
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) -
          secondOrderExplicitFormulaIntegrand x
            (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ K := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have habs : |t| ≤ T := abs_le.mpr ⟨by linarith [ht.1], ht.2⟩
    simpa [K, T] using
      norm_secondOrderExplicitFormulaIntegrand_sub_odd_vertical_le_of_pos
        hx hy hxy hT habs hsmall
  have hdiffIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun t : ℝ =>
      secondOrderExplicitFormulaIntegrand y
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I) -
        secondOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I))
    (a := -T) (b := T) (C := K) hpoint
  have hyInt :=
    intervalIntegrable_secondOrderExplicitFormulaIntegrand_odd_vertical_of_pos
      (T := T) (N := N) hy
  have hxInt :=
    intervalIntegrable_secondOrderExplicitFormulaIntegrand_odd_vertical_of_pos
      (T := T) (N := N) hx
  rw [abs_of_nonneg (by linarith : 0 ≤ T - -T)] at hdiffIntegral
  unfold secondOrderLeftXDifference
  change ‖(∫ t : ℝ in (-T)..T,
      secondOrderExplicitFormulaIntegrand y
        (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)) -
      ∫ t : ℝ in (-T)..T,
        secondOrderExplicitFormulaIntegrand x
          (((-(2 * (N : ℝ) + 1) : ℝ) : ℂ) + (t : ℂ) * I)‖ ≤ _
  rw [← intervalIntegral.integral_sub hyInt hxInt]
  convert hdiffIntegral using 1 <;> dsimp [K, T] <;> ring

/-- A good-height rectangle with negative-odd left edge has every candidate
pole (`0`, `1`, or a zeta zero) in its strict interior.  The parity argument
excludes trivial zeros from the left edge, while `goodHeight` excludes
nontrivial zeros from the horizontal edges. -/
theorem secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
    {N : ℕ} {T c : ℝ} (hT : 0 < T) (hc : 1 < c)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    ∀ p ∈
      ([[(-(2 * (N : ℝ) + 1)), c]] ×ℂ [[-T, T]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        -(2 * (N : ℝ) + 1) < p.re ∧ p.re < c ∧
          -T < p.im ∧ p.im < T := by
  intro p hp hclass
  rcases hclass with rfl | rfl | hpzero
  · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    simpa using
      (show -(2 * (N : ℝ) + 1) < (0 : ℝ) ∧ 0 < c ∧ -T < 0 ∧ 0 < T from
        ⟨by linarith, by linarith, by linarith, hT⟩)
  · have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
    simpa using
      (show -(2 * (N : ℝ) + 1) < (1 : ℝ) ∧ 1 < c ∧ -T < 0 ∧ 0 < T from
        ⟨by linarith, hc, by linarith, hT⟩)
  · have hp' := hp
    simp only [Complex.mem_reProdIm] at hp'
    have ha_le_c : -(2 * (N : ℝ) + 1) ≤ c := by
      have hN : 0 ≤ (N : ℝ) := Nat.cast_nonneg N
      linarith
    rw [Set.uIcc_of_le ha_le_c] at hp'
    rw [Set.uIcc_of_le (by linarith : -T ≤ T)] at hp'
    by_cases htriv : ∃ n : ℕ, p = -2 * ((n : ℂ) + 1)
    · rcases htriv with ⟨n, hn⟩
      have hre := congrArg Complex.re hn
      have him := congrArg Complex.im hn
      norm_num at hre him
      have hre_lower : -(2 * (N : ℝ) + 1) < p.re := by
        by_contra hnot
        have hre_eq : p.re = -(2 * (N : ℝ) + 1) := by
          linarith [hp'.1.1]
        rw [hre_eq] at hre
        have hnat : 2 * N + 1 = 2 * (n + 1) := by
          exact_mod_cast (by linarith :
            (2 * (N : ℝ) + 1) = 2 * ((n : ℝ) + 1))
        omega
      exact ⟨hre_lower, by linarith [hp'.1.2], by linarith [hp'.2.1],
        by linarith [hp'.2.2]⟩
    · have hre_pos : 0 < p.re := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_re_le_zero
          (le_of_not_gt hnot) (by simpa [not_exists] using htriv)) hpzero
      have hre_lt_one : p.re < 1 := by
        by_contra hnot
        exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hpzero
      have habs_le : |p.im| ≤ T := abs_le.mpr hp'.2
      have habs_ne : |p.im| ≠ T :=
        hgood p ⟨hpzero, hre_pos, hre_lt_one⟩
      have him_strict := abs_lt.mp (lt_of_le_of_ne habs_le habs_ne)
      exact ⟨by linarith, by linarith, him_strict.1, him_strict.2⟩

/-- A logarithmic-derivative bound on one horizontal point gains a second
factor of the height in the denominator for the second-order Perron kernel. -/
lemma norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    {x σ b t K : ℝ} (hx : 1 ≤ x) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlog : ‖logDeriv riemannZeta ((σ : ℂ) + I * t)‖ ≤ K) :
    ‖secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + I * t)‖ ≤
      K * x ^ b / |t| ^ 2 := by
  let s : ℂ := (σ : ℂ) + I * t
  have hfirst := norm_explicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
    hx hσ ht hK hlog
  have hline : |t| ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    simpa [s] using him
  have hnum : 0 ≤ K * x ^ b :=
    mul_nonneg hK (Real.rpow_nonneg (zero_le_one.trans hx) _)
  change ‖explicitFormulaIntegrand x s / s‖ ≤ _
  rw [norm_div]
  calc
    ‖explicitFormulaIntegrand x s‖ / ‖s‖ ≤
        (K * x ^ b / |t|) / ‖s‖ :=
      div_le_div_of_nonneg_right hfirst (norm_nonneg s)
    _ ≤ (K * x ^ b / |t|) / |t| :=
      div_le_div_of_nonneg_left (div_nonneg hnum ht.le) ht hline
    _ = K * x ^ b / |t| ^ 2 := by ring

/-- Pointwise horizontal estimate after subtracting the two endpoint kernels
before taking norms.  Relative to separate endpoint estimates, this retains
the logarithmic increment `log y - log x`; one height denominator is spent
controlling the exponential difference. -/
lemma norm_secondOrderExplicitFormulaIntegrand_sub_horizontal_le
    {x y σ b t K : ℝ}
    (hx : 1 ≤ x) (hy : 0 < y) (hσ : σ ≤ b) (ht : 0 < |t|)
    (hK : 0 ≤ K)
    (hlogDeriv :
      ‖logDeriv riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K)
    (hlog : 0 ≤ Real.log y - Real.log x)
    (hsmall :
      ‖((σ : ℂ) + (t : ℂ) * I)‖ *
          (Real.log y - Real.log x) ≤ 1) :
    ‖secondOrderExplicitFormulaIntegrand y
          ((σ : ℂ) + (t : ℂ) * I) -
        secondOrderExplicitFormulaIntegrand x
          ((σ : ℂ) + (t : ℂ) * I)‖ ≤
      2 * K * x ^ b * (Real.log y - Real.log x) / |t| := by
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    exact (ne_of_gt ht) (abs_eq_zero.mpr him)
  let d : ℝ := Real.log y - Real.log x
  have hd : 0 ≤ d := hlog
  have hsNormPos : 0 < ‖s‖ := norm_pos_iff.mpr hs0
  have hfac :
      (y : ℂ) ^ s - (x : ℂ) ^ s =
        (x : ℂ) ^ s * (Complex.exp ((d : ℂ) * s) - 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero
        (Complex.ofReal_ne_zero.mpr (zero_lt_one.trans_le hx).ne')]
    rw [← Complex.ofReal_log hy.le,
      ← Complex.ofReal_log (zero_lt_one.trans_le hx).le]
    rw [show (Real.log y : ℂ) * s =
        (Real.log x : ℂ) * s + (d : ℂ) * s by
          simp only [d, Complex.ofReal_sub]
          ring]
    rw [Complex.exp_add]
    ring
  have hzNorm : ‖(d : ℂ) * s‖ = d * ‖s‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  have hzSmall : ‖(d : ℂ) * s‖ ≤ 1 := by
    rw [hzNorm, mul_comm]
    exact hsmall
  have hrem : ‖Complex.exp ((d : ℂ) * s) - 1‖ ≤ 2 * (d * ‖s‖) := by
    simpa [abs_of_nonneg hd] using Complex.norm_exp_sub_one_le hzSmall
  have hfactor :
      ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
        2 * x ^ s.re * (Real.log y - Real.log x) / ‖s‖ := by
    rw [hfac, norm_div, norm_mul, norm_pow,
      Complex.norm_cpow_eq_rpow_re_of_pos (zero_lt_one.trans_le hx)]
    calc
      x ^ s.re * ‖Complex.exp ((d : ℂ) * s) - 1‖ / ‖s‖ ^ 2 ≤
          x ^ s.re * (2 * (d * ‖s‖)) / ‖s‖ ^ 2 := by
        gcongr
      _ = 2 * x ^ s.re * (Real.log y - Real.log x) / ‖s‖ := by
        dsimp [d]
        field_simp [ne_of_gt hsNormPos]
  have hsre : s.re = σ := by simp [s]
  have hpow : x ^ s.re ≤ x ^ b := by
    rw [hsre]
    exact Real.rpow_le_rpow_of_exponent_le hx hσ
  have htNorm : |t| ≤ ‖s‖ := by
    have him := Complex.abs_im_le_norm s
    simpa [s] using him
  have hd' : 0 ≤ Real.log y - Real.log x := hlog
  have hpowNonneg : 0 ≤ x ^ b :=
    Real.rpow_nonneg (zero_le_one.trans hx) _
  have hfactor' :
      ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
        2 * x ^ b * (Real.log y - Real.log x) / |t| := by
    calc
      ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
          2 * x ^ s.re * (Real.log y - Real.log x) / ‖s‖ := hfactor
      _ ≤ 2 * x ^ b * (Real.log y - Real.log x) / ‖s‖ := by
        gcongr
      _ ≤ 2 * x ^ b * (Real.log y - Real.log x) / |t| := by
        exact div_le_div_of_nonneg_left
          (mul_nonneg (mul_nonneg (by norm_num) hpowNonneg) hd')
          ht htNorm
  have hrewrite :
      secondOrderExplicitFormulaIntegrand y s -
          secondOrderExplicitFormulaIntegrand x s =
        -logDeriv riemannZeta s *
          (((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2) := by
    unfold secondOrderExplicitFormulaIntegrand explicitFormulaIntegrand
    ring
  rw [hrewrite, norm_mul]
  calc
    ‖-logDeriv riemannZeta s‖ *
        ‖((y : ℂ) ^ s - (x : ℂ) ^ s) / s ^ 2‖ ≤
      K * (2 * x ^ b * (Real.log y - Real.log x) / |t|) := by
        exact mul_le_mul (by simpa [s] using hlogDeriv) hfactor'
          (norm_nonneg _) hK
    _ = 2 * K * x ^ b * (Real.log y - Real.log x) / |t| := by
      ring

/-- A nonzero zero-free horizontal segment makes the second-order integrand
interval integrable.  This is the linearity input needed to combine the two
endpoint integrals before applying the norm. -/
lemma intervalIntegrable_secondOrderExplicitFormulaIntegrand_horizontal
    {x a b t : ℝ} (hx : 0 < x) (ht : 0 < |t|)
    (hzeta : ∀ σ ∈ Set.uIcc a b,
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0) :
    IntervalIntegrable
      (fun σ : ℝ =>
        secondOrderExplicitFormulaIntegrand x
          ((σ : ℂ) + (t : ℂ) * I)) MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable (μ := MeasureTheory.volume)
  intro σ hσ
  let s : ℂ := (σ : ℂ) + (t : ℂ) * I
  have hs0 : s ≠ 0 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    exact (ne_of_gt ht) (abs_eq_zero.mpr him)
  have hs1 : s ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp [s] at him
    exact (ne_of_gt ht) (abs_eq_zero.mpr him)
  have hanalytic :
      AnalyticAt ℂ (secondOrderExplicitFormulaIntegrand x) s := by
    simpa [secondOrderExplicitFormulaIntegrand] using
      (analyticAt_explicitFormulaIntegrand_of_ne_zero_of_ne_one_of_zeta_ne_zero
          hx hs0 hs1 (hzeta σ hσ)).div analyticAt_id hs0
  have hmap :
      ContinuousAt (fun r : ℝ => (r : ℂ) + (t : ℂ) * I) σ := by
    fun_prop
  simpa [s, Function.comp_def] using
    (hanalytic.continuousAt.comp_of_eq hmap (by simp [s])).continuousWithinAt

/-- Good heights control the horizontal endpoint difference after the
endpoint kernels are subtracted.  Under the uniform small-increment condition
the horizontal budget is proportional to
`log ((x+h)/x) / T`, instead of a sum of two independent `T⁻²` endpoint
budgets. -/
theorem
    exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_increment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h a b : ℝ},
            1 ≤ x → 0 ≤ h → -1 ≤ a → a ≤ b → b ≤ 2 →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            ∀ t : ℝ, |t| = T →
              ‖secondOrderHorizontalXDifference x (x + h) a b t‖ ≤
                (2 * C * x ^ (2 : ℝ) *
                    Real.log ((x + h) / x) *
                    (1 + Real.log (A + 6)) ^ 2 / T) *
                  (b - a) := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hlogDeriv⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h a b hx hh ha hab hb hsmall t ht
  have hTpos : 0 < T := by linarith [hT.1]
  have htpos : 0 < |t| := by rw [ht]; exact hTpos
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hypos : 0 < x + h := by linarith
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hxpos).2 (by linarith)
  have hlognonneg : 0 ≤ Real.log ((x + h) / x) :=
    Real.log_nonneg hratio
  let K : ℝ :=
    2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
      (1 + Real.log (A + 6)) ^ 2 / T
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hpoint : ∀ σ ∈ Set.uIoc a b,
      ‖secondOrderExplicitFormulaIntegrand (x + h)
          ((σ : ℂ) + (t : ℂ) * I) -
        secondOrderExplicitFormulaIntegrand x
          ((σ : ℂ) + (t : ℂ) * I)‖ ≤ K := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hσbounds : |σ| ≤ 2 := by
      rw [abs_le]
      exact ⟨by linarith [ha, hσ.1], le_trans hσ.2 hb⟩
    have hsNorm :
        ‖((σ : ℂ) + (t : ℂ) * I)‖ ≤ T + 2 := by
      calc
        ‖((σ : ℂ) + (t : ℂ) * I)‖ ≤
            ‖(σ : ℂ)‖ + ‖(t : ℂ) * I‖ := norm_add_le _ _
        _ = |σ| + |t| := by
          rw [norm_mul, norm_I, mul_one, Complex.norm_real,
            Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ T + 2 := by rw [ht]; linarith
    have hpointSmall :
        ‖((σ : ℂ) + (t : ℂ) * I)‖ *
            (Real.log (x + h) - Real.log x) ≤ 1 := by
      rw [← Real.log_div hypos.ne' hxpos.ne']
      exact (mul_le_mul_of_nonneg_right hsNorm hlognonneg).trans hsmall
    have hpointBound :=
      norm_secondOrderExplicitFormulaIntegrand_sub_horizontal_le
        (x := x) (y := x + h) (σ := σ) (b := 2)
        (t := t)
        (K := C * (1 + Real.log (A + 6)) ^ 2)
        hx hypos (le_trans hσ.2 hb) htpos
        (mul_nonneg hC (sq_nonneg _))
        (by
          simpa [mul_comm] using
            hlogDeriv t ht σ (le_trans ha hσ.1.le)
              (le_trans hσ.2 hb))
        (by
          rw [← Real.log_div hypos.ne' hxpos.ne']
          exact hlognonneg)
        hpointSmall
    rw [ht] at hpointBound
    rw [← Real.log_div hypos.ne' hxpos.ne'] at hpointBound
    dsimp [K]
    convert hpointBound using 1 <;> ring
  have hdiffIntegral :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun σ : ℝ =>
        secondOrderExplicitFormulaIntegrand (x + h)
            ((σ : ℂ) + (t : ℂ) * I) -
          secondOrderExplicitFormulaIntegrand x
            ((σ : ℂ) + (t : ℂ) * I))
      (a := a) (b := b) (C := K) hpoint
  have hzeta : ∀ σ ∈ Set.uIcc a b,
      riemannZeta ((σ : ℂ) + (t : ℂ) * I) ≠ 0 := by
    intro σ _hσ
    simpa [mul_comm] using
      riemannZeta_ne_zero_on_goodHeight_horizontal
        (T := T) (t := t) (σ := σ) hTpos ht hgood
  have hyInt :=
    intervalIntegrable_secondOrderExplicitFormulaIntegrand_horizontal
      hypos htpos hzeta
  have hxInt :=
    intervalIntegrable_secondOrderExplicitFormulaIntegrand_horizontal
      hxpos htpos hzeta
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hdiffIntegral
  unfold secondOrderHorizontalXDifference
  rw [← intervalIntegral.integral_sub hyInt hxInt]
  simpa [K] using hdiffIntegral

/-- In every unit height interval, one selected good height and one absolute
constant control the full central horizontal endpoint difference for every
pair of samples at least one and every interval contained in `[-1,2]`. -/
theorem
    exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x y a b : ℝ}, 1 ≤ x → 1 ≤ y → -1 ≤ a → a ≤ b → b ≤ 2 →
            ∀ t : ℝ, |t| = T →
              ‖secondOrderHorizontalXDifference x y a b t‖ ≤
                ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                  (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                  (b - a) := by
  rcases exists_goodHeight_Icc_norm_logDeriv_central_band_le_log_sq with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hlog⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x y a b hx hy ha hab hb t ht
  have hTabs : 0 < |t| := by rw [ht]; linarith [hT.1]
  have hK : 0 ≤ C * (1 + Real.log (A + 6)) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  let Ky : ℝ := C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  let Kx : ℝ := C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  have hyPoint : ∀ σ ∈ Set.uIoc a b,
      ‖secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I)‖ ≤ Ky := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hpoint :=
      norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
        (b := 2) hy (le_trans hσ.2 hb) hTabs hK
          (hlog t ht σ (le_trans ha hσ.1.le) (le_trans hσ.2 hb))
    rw [ht] at hpoint
    simpa [Ky, mul_comm, mul_left_comm, mul_assoc] using hpoint
  have hxPoint : ∀ σ ∈ Set.uIoc a b,
      ‖secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I)‖ ≤ Kx := by
    intro σ hσ
    rw [Set.uIoc_of_le hab] at hσ
    have hpoint :=
      norm_secondOrderExplicitFormulaIntegrand_horizontal_le_of_logDeriv_le_of_re_le
        (b := 2) hx (le_trans hσ.2 hb) hTabs hK
          (hlog t ht σ (le_trans ha hσ.1.le) (le_trans hσ.2 hb))
    rw [ht] at hpoint
    simpa [Kx, mul_comm, mul_left_comm, mul_assoc] using hpoint
  have hyIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I))
    (a := a) (b := b) (C := Ky) hyPoint
  have hxIntegral := intervalIntegral.norm_integral_le_of_norm_le_const
    (f := fun σ : ℝ => secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I))
    (a := a) (b := b) (C := Kx) hxPoint
  rw [abs_of_nonneg (sub_nonneg.mpr hab)] at hyIntegral hxIntegral
  unfold secondOrderHorizontalXDifference
  calc
    _ ≤ ‖∫ σ : ℝ in a..b,
          secondOrderExplicitFormulaIntegrand y ((σ : ℂ) + t * I)‖ +
        ‖∫ σ : ℝ in a..b,
          secondOrderExplicitFormulaIntegrand x ((σ : ℂ) + t * I)‖ :=
      norm_sub_le _ _
    _ ≤ Ky * (b - a) + Kx * (b - a) := add_le_add hyIntegral hxIntegral
    _ = _ := by dsimp [Ky, Kx]; ring

/-- Endpoint-specialized compatibility form of the uniform selected-height
horizontal estimate. -/
theorem exists_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le
    {x y a b : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (ha : -1 ≤ a)
    (hab : a ≤ b) (hb : b ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ t : ℝ, |t| = T →
            ‖secondOrderHorizontalXDifference x y a b t‖ ≤
              ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                (b - a) := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hhorizontal⟩
  exact ⟨T, hT, hgood, hhorizontal hx hy ha hab hb⟩

/-- The full second-order contour-remainder difference is controlled by the
three actual edge differences. This is an exact finite-height budget, not an
asymptotic estimate. -/
theorem norm_secondOrderContourRemainder_sub_le_edgeDifferences
    (x y a c W : ℝ) :
    ‖secondOrderContourRemainder y a c W -
        secondOrderContourRemainder x a c W‖ ≤
      (‖secondOrderHorizontalXDifference x y a c (-(2 * Real.pi * W))‖ +
          ‖secondOrderHorizontalXDifference x y a c (2 * Real.pi * W)‖ +
          ‖secondOrderLeftXDifference x y a W‖) /
        (2 * Real.pi) := by
  let B := secondOrderHorizontalXDifference x y a c (-(2 * Real.pi * W))
  let T := secondOrderHorizontalXDifference x y a c (2 * Real.pi * W)
  let L := secondOrderLeftXDifference x y a W
  have hremainder :
      secondOrderContourRemainder y a c W -
          secondOrderContourRemainder x a c W =
        (B - T - I * L) / (2 * Real.pi * I) := by
    dsimp [B, T, L, secondOrderHorizontalXDifference,
      secondOrderLeftXDifference, secondOrderContourRemainder]
    ring
  rw [hremainder, norm_div]
  have hden : ‖(2 : ℂ) * (Real.pi : ℂ) * I‖ = 2 * Real.pi := by
    rw [norm_mul, norm_I, mul_one, norm_mul, norm_ofNat, Complex.norm_real,
      Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hden]
  apply (div_le_div_iff_of_pos_right (mul_pos (by norm_num) Real.pi_pos)).2
  calc
    ‖B - T - I * L‖ ≤ ‖B - T‖ + ‖I * L‖ := norm_sub_le _ _
    _ ≤ (‖B‖ + ‖T‖) + ‖L‖ := by
      gcongr
      · exact norm_sub_le B T
      · simp
    _ = ‖B‖ + ‖T‖ + ‖L‖ := rfl

/-- One absolute constant and one good height in each unit interval control
the complete negative-one contour-remainder difference for every pair of
samples at least one and every right edge in `(1,2]`.  The same selected height
also supplies the required boundary safety. -/
theorem
    exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x y c : ℝ}, 1 ≤ x → 1 ≤ y → 1 < c → c ≤ 2 →
            (∀ p ∈
              ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
                -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
            ‖secondOrderContourRemainder y (-1) c (T / (2 * Real.pi)) -
                secondOrderContourRemainder x (-1) c (T / (2 * Real.pi))‖ ≤
              (2 *
                  (((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                      (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                    (c - (-1))) +
                (secondOrderOddVerticalBound y 0 T +
                    secondOrderOddVerticalBound x 0 T) *
                  (2 * T)) /
                (2 * Real.pi) := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_le with
    ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hhorizontalAll⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x y c hx hy hc hc2
  have hhorizontal :
      ∀ t : ℝ, |t| = T →
        ‖secondOrderHorizontalXDifference x y (-1) c t‖ ≤
          ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
            (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
            (c - (-1)) :=
    hhorizontalAll hx hy (by norm_num) (by linarith) hc2
  have hTpos : 0 < T := by linarith [hT.1]
  have hboundary :
      ∀ p ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
          -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T := by
    simpa using
      (secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
        (N := 0) hTpos hc hgood)
  let K : ℝ :=
    ((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
      (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
        (c - (-1))
  let L : ℝ :=
    (secondOrderOddVerticalBound y 0 T +
      secondOrderOddVerticalBound x 0 T) * (2 * T)
  have hbottom :
      ‖secondOrderHorizontalXDifference x y (-1) c (-T)‖ ≤ K := by
    exact hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTpos])
  have htop :
      ‖secondOrderHorizontalXDifference x y (-1) c T‖ ≤ K := by
    exact hhorizontal T (abs_of_pos hTpos)
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp [Real.pi_ne_zero]
  have hleft :
      ‖secondOrderLeftXDifference x y (-1) (T / (2 * Real.pi))‖ ≤ L := by
    have hraw := norm_secondOrderLeftXDifference_odd_le_of_pos
      (N := 0) (lt_of_lt_of_le zero_lt_one hx)
        (lt_of_lt_of_le zero_lt_one hy)
        (div_nonneg hTpos.le hden.le)
    simpa [hscale, L] using hraw
  have hremainder :=
    norm_secondOrderContourRemainder_sub_le_edgeDifferences
      x y (-1) c (T / (2 * Real.pi))
  rw [hscale] at hremainder
  refine ⟨hboundary, ?_⟩
  calc
    ‖secondOrderContourRemainder y (-1) c (T / (2 * Real.pi)) -
        secondOrderContourRemainder x (-1) c (T / (2 * Real.pi))‖ ≤
        (‖secondOrderHorizontalXDifference x y (-1) c (-T)‖ +
            ‖secondOrderHorizontalXDifference x y (-1) c T‖ +
            ‖secondOrderLeftXDifference x y (-1) (T / (2 * Real.pi))‖) /
          (2 * Real.pi) := hremainder
    _ ≤ (K + K + L) / (2 * Real.pi) := by
      exact (div_le_div_iff_of_pos_right hden).2
        (add_le_add (add_le_add hbottom htop) hleft)
    _ = _ := by
      dsimp [K, L]
      ring

/-- Endpoint-specialized compatibility form of the uniform selected-height
negative-one contour-remainder estimate. -/
theorem exists_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le
    {x y c : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y)
    (hc : 1 < c) (hc2 : c ≤ 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          (∀ p ∈
            ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
            p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
              -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
          ‖secondOrderContourRemainder y (-1) c (T / (2 * Real.pi)) -
              secondOrderContourRemainder x (-1) c (T / (2 * Real.pi))‖ ≤
            (2 *
                (((C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
                    (C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
                  (c - (-1))) +
              (secondOrderOddVerticalBound y 0 T +
                  secondOrderOddVerticalBound x 0 T) *
                (2 * T)) /
              (2 * Real.pi) := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  rcases hbound hx hy hc hc2 with ⟨hboundary, hremainder⟩
  exact ⟨T, hT, hgood, hboundary, hremainder⟩

/-- Concrete `T^-2` control of the change in the upper right horizontal edge
when the smoothing endpoint changes from `x` to `y`. -/
theorem norm_secondOrderHorizontalXDifference_right_le
    {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖secondOrderHorizontalXDifference x y (1 + ε) c T‖ ≤
      (vonMangoldtLSeriesNorm ε * y ^ c / T ^ 2) * (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) * (c - (1 + ε)) := by
  unfold secondOrderHorizontalXDifference
  exact (norm_sub_le _ _).trans (add_le_add
    (norm_horizontal_right_secondOrderContour_le hy hε hc hT)
    (norm_horizontal_right_secondOrderContour_le hx hε hc hT))

/-- Concrete `T^-2` control of the corresponding lower right horizontal edge
difference. -/
theorem norm_secondOrderHorizontalXDifference_right_neg_height_le
    {x y ε c T : ℝ} (hx : 1 ≤ x) (hy : 1 ≤ y) (hε : 0 < ε)
    (hc : 1 + ε ≤ c) (hT : 0 < T) :
    ‖secondOrderHorizontalXDifference x y (1 + ε) c (-T)‖ ≤
      (vonMangoldtLSeriesNorm ε * y ^ c / T ^ 2) * (c - (1 + ε)) +
        (vonMangoldtLSeriesNorm ε * x ^ c / T ^ 2) * (c - (1 + ε)) := by
  unfold secondOrderHorizontalXDifference
  simpa [sub_eq_add_neg] using
    (norm_sub_le
      (∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand y ((σ : ℂ) - T * I))
      (∫ σ : ℝ in (1 + ε)..c,
        secondOrderExplicitFormulaIntegrand x ((σ : ℂ) - T * I))).trans
      (add_le_add
        (norm_horizontal_right_secondOrderContour_neg_height_le hy hε hc hT)
        (norm_horizontal_right_secondOrderContour_neg_height_le hx hε hc hT))

end ExplicitFormulaResidues

/-- If a complex approximation controls the first Riesz mean at `x` and
`x + h`, its real-part finite difference gives explicit endpoint bounds for
`chebyshevPsi`. The theorem is uniform in the smoothing width `h` and the
external height parameter `T`. -/
theorem chebyshevPsi_bounds_of_smoothedApproximation
    (approx : ℝ → ℝ → ℂ) (error : ℝ → ℝ → ℝ)
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hxError : ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ ≤ error x T)
    (hyError : ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
      error (x + h) T) :
    chebyshevPsi x ≤
        ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ∧
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
        chebyshevPsi (x + h) := by
  have hxy : x < x + h := by linarith
  have hratio : 1 < (x + h) / x := (lt_div_iff₀ hx).2 (by linarith)
  have hlog : 0 < Real.log ((x + h) / x) := Real.log_pos hratio
  have hxReal : |(approx x T).re - smoothedChebyshevPsi x| ≤ error x T := by
    calc
      |(approx x T).re - smoothedChebyshevPsi x| =
          |(approx x T - (smoothedChebyshevPsi x : ℂ)).re| := by simp
      _ ≤ ‖approx x T - (smoothedChebyshevPsi x : ℂ)‖ := abs_re_le_norm _
      _ ≤ error x T := hxError
  have hyReal : |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| ≤
      error (x + h) T := by
    calc
      |(approx (x + h) T).re - smoothedChebyshevPsi (x + h)| =
          |(approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)).re| := by simp
      _ ≤ ‖approx (x + h) T - (smoothedChebyshevPsi (x + h) : ℂ)‖ :=
        abs_re_le_norm _
      _ ≤ error (x + h) T := hyError
  have hUpper : smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x ≤
      (approx (x + h) T).re - (approx x T).re +
        (error x T + error (x + h) T) := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hLower :
      (approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T) ≤
        smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x := by
    rcases abs_le.mp hxReal with ⟨hxLower, hxUpper⟩
    rcases abs_le.mp hyReal with ⟨hyLower, hyUpper⟩
    linarith
  have hRiesz := chebyshevPsi_le_rieszDifference_div_log_le hx hxy
  constructor
  · calc
      chebyshevPsi x ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := hRiesz.1
      _ ≤ ((approx (x + h) T).re - (approx x T).re +
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hUpper
  · calc
      ((approx (x + h) T).re - (approx x T).re -
          (error x T + error (x + h) T)) /
            Real.log ((x + h) / x) ≤
          (smoothedChebyshevPsi (x + h) - smoothedChebyshevPsi x) /
            Real.log ((x + h) / x) := (div_le_div_iff_of_pos_right hlog).2 hLower
      _ ≤ chebyshevPsi (x + h) := hRiesz.2

namespace ExplicitFormulaResidues

/-- The explicit Perron truncation error appearing in the finite-height
second-order formula. This excludes the three shifted contour edges, which are
part of the approximation itself. -/
noncomputable def secondOrderPerronError (x c W : ℝ) : ℝ :=
  ∑' n : ℕ, vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W)

/-- The raw second-order Perron tail factors exactly into an `x,W` scale and
the absolute von Mangoldt Dirichlet-series norm on `Re(s)=c`. -/
theorem secondOrderPerronError_eq_vonMangoldtLSeriesNorm
    {x c W : ℝ} (hx : 0 < x) (hc : 1 < c) (hW : 0 < W) :
    secondOrderPerronError x c W =
      (x ^ c / (2 * Real.pi ^ 2 * W)) *
        vonMangoldtLSeriesNorm (c - 1) := by
  let coeff : ℕ → ℂ :=
    fun n => (ArithmeticFunction.vonMangoldt n : ℂ)
  let B : ℕ → ℝ := fun n =>
    vonMangoldt n * (x / n) ^ c / (2 * Real.pi ^ 2 * W)
  have hnorm_summable : Summable fun n =>
      ‖LSeries.term coeff (c : ℂ) n‖ := by
    have hs := ArithmeticFunction.LSeriesSummable_vonMangoldt
      (s := (c : ℂ)) (by simpa using hc)
    rw [LSeriesSummable, ← summable_norm_iff] at hs
    simpa [coeff] using hs
  have hB_eq (n : ℕ) : B n =
      (x ^ c / (2 * Real.pi ^ 2 * W)) *
        ‖LSeries.term coeff (c : ℂ) n‖ := by
    by_cases hn : n = 0
    · subst n
      simp [B, LSeries.term, vonMangoldt_eq_mathlib]
    · have hn_pos : 0 < (n : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hn
      dsimp [B, coeff]
      rw [LSeries.norm_term_eq, vonMangoldt_eq_mathlib,
        Real.div_rpow hx.le hn_pos.le]
      simp only [hn, if_false, Complex.ofReal_re]
      rw [norm_real, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
      field_simp
  calc
    secondOrderPerronError x c W = ∑' n : ℕ, B n := by rfl
    _ = ∑' n : ℕ,
        (x ^ c / (2 * Real.pi ^ 2 * W)) *
          ‖LSeries.term coeff (c : ℂ) n‖ :=
      tsum_congr hB_eq
    _ = (x ^ c / (2 * Real.pi ^ 2 * W)) *
        ∑' n : ℕ, ‖LSeries.term coeff (c : ℂ) n‖ :=
      tsum_mul_left
    _ = (x ^ c / (2 * Real.pi ^ 2 * W)) *
        vonMangoldtLSeriesNorm (c - 1) := by
      congr 1
      unfold vonMangoldtLSeriesNorm
      apply tsum_congr
      intro n
      congr 2
      push_cast
      ring

/-- Explicit `ε,W` upper bound for the second-order Perron truncation tail.
This is a proved analytic envelope, not a numerical optimizer input. -/
theorem secondOrderPerronError_le_explicit
    {x ε W : ℝ} (hx : 0 < x) (hε : 0 < ε) (hW : 0 < W) :
    secondOrderPerronError x (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
        ((2 / ε) * (1 + 2 / ε)) := by
  rw [secondOrderPerronError_eq_vonMangoldtLSeriesNorm
    hx (by linarith) hW]
  have hnorm :=
    vonMangoldtLSeriesNorm_le_two_div_mul_one_add_two_div hε
  have hscale :
      0 ≤ x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) := by
    positivity
  simpa only [add_sub_cancel_left] using
    mul_le_mul_of_nonneg_left hnorm hscale

/-- The sum of the two endpoint Perron errors used by the Riesz sandwich has
one explicit common `ε,W` budget. -/
theorem secondOrderPerronError_add_le_explicit
    {x h ε W : ℝ} (hx : 0 < x) (hh : 0 < h)
    (hε : 0 < ε) (hW : 0 < W) :
    secondOrderPerronError x (1 + ε) W +
        secondOrderPerronError (x + h) (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) +
          (x + h) ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
        ((2 / ε) * (1 + 2 / ε)) := by
  have hy : 0 < x + h := by linarith
  have hxbound := secondOrderPerronError_le_explicit hx hε hW
  have hybound := secondOrderPerronError_le_explicit hy hε hW
  calc
    secondOrderPerronError x (1 + ε) W +
        secondOrderPerronError (x + h) (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
          ((2 / ε) * (1 + 2 / ε)) +
        ((x + h) ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
          ((2 / ε) * (1 + 2 / ε)) :=
      add_le_add hxbound hybound
    _ = _ := by ring

/-- On the classical moving Perron line `c = 1 + 1 / log x`, the raw
second-order tail is `O(x log^2 x / W)` with a fully explicit coefficient. -/
theorem secondOrderPerronError_moving_line_le
    {x W : ℝ} (hx : 1 < x) (hW : 0 < W) :
    secondOrderPerronError x (1 + 1 / Real.log x) W ≤
      (Real.exp 1 * x / (2 * Real.pi ^ 2 * W)) *
        (4 * (1 + Real.log x) ^ 2) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hx1 : x ≠ 1 := ne_of_gt hx
  have hlog : 0 < Real.log x := Real.log_pos hx
  have heps : 0 < 1 / Real.log x := by positivity
  have hraw :=
    secondOrderPerronError_le_explicit hx0 heps hW
  have hxpow :
      x ^ (1 + 1 / Real.log x) = Real.exp 1 * x := by
    rw [Real.rpow_add hx0, Real.rpow_one]
    rw [one_div, Real.rpow_inv_log hx0 hx1]
    ring
  have heps_inv :
      2 / (1 / Real.log x) = 2 * Real.log x := by
    field_simp [hlog.ne']
  have hpoly :
      (2 * Real.log x) * (1 + 2 * Real.log x) ≤
        4 * (1 + Real.log x) ^ 2 := by
    nlinarith [sq_nonneg (Real.log x)]
  have hscale :
      0 ≤ Real.exp 1 * x / (2 * Real.pi ^ 2 * W) := by
    positivity
  rw [hxpow, heps_inv] at hraw
  exact hraw.trans (mul_le_mul_of_nonneg_left hpoly hscale)

/-- A common moving line based at the upper endpoint `x+h` controls both
Perron tails in the Riesz finite difference by one explicit budget. -/
theorem secondOrderPerronError_add_moving_line_le
    {x h W : ℝ} (hx : 1 < x) (hh : 0 < h) (hW : 0 < W) :
    secondOrderPerronError x
          (1 + 1 / Real.log (x + h)) W +
        secondOrderPerronError (x + h)
          (1 + 1 / Real.log (x + h)) W ≤
      (2 * (Real.exp 1 * (x + h) /
          (2 * Real.pi ^ 2 * W))) *
        (4 * (1 + Real.log (x + h)) ^ 2) := by
  let y : ℝ := x + h
  let ell : ℝ := Real.log y
  let ε : ℝ := 1 / ell
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 < y := by dsimp [y]; linarith
  have hy0 : 0 < y := zero_lt_one.trans hy
  have hy1 : y ≠ 1 := ne_of_gt hy
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hell : 0 < ell := by
    dsimp [ell]
    exact Real.log_pos hy
  have heps : 0 < ε := by dsimp [ε]; positivity
  have hc0 : 0 ≤ 1 + ε := by linarith
  have hraw :=
    secondOrderPerronError_add_le_explicit
      (x := x) (h := h) (ε := ε) (W := W) hx0 hh heps hW
  have hypow :
      y ^ (1 + ε) = Real.exp 1 * y := by
    dsimp [ε, ell]
    rw [Real.rpow_add hy0, Real.rpow_one]
    rw [one_div, Real.rpow_inv_log hy0 hy1]
    ring
  have hxpow_le :
      x ^ (1 + ε) ≤ Real.exp 1 * y := by
    rw [← hypow]
    exact Real.rpow_le_rpow hx0.le hxy hc0
  have hden :
      0 < 2 * Real.pi ^ 2 * W := by positivity
  have hscale :
      x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) +
          y ^ (1 + ε) / (2 * Real.pi ^ 2 * W) ≤
        2 * (Real.exp 1 * y / (2 * Real.pi ^ 2 * W)) := by
    rw [hypow]
    have hxdiv :
        x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) ≤
          Real.exp 1 * y / (2 * Real.pi ^ 2 * W) :=
      div_le_div_of_nonneg_right hxpow_le hden.le
    linarith
  have heps_inv :
      2 / ε = 2 * ell := by
    dsimp [ε]
    field_simp [hell.ne']
  have hmajor_nonneg :
      0 ≤ (2 / ε) * (1 + 2 / ε) := by positivity
  have hpoly :
      (2 * ell) * (1 + 2 * ell) ≤
        4 * (1 + ell) ^ 2 := by
    nlinarith [sq_nonneg ell]
  have hscale_nonneg :
      0 ≤ 2 * (Real.exp 1 * y /
        (2 * Real.pi ^ 2 * W)) := by positivity
  change
    secondOrderPerronError x (1 + ε) W +
        secondOrderPerronError y (1 + ε) W ≤ _ at hraw
  change
    secondOrderPerronError x (1 + ε) W +
        secondOrderPerronError y (1 + ε) W ≤
      (2 * (Real.exp 1 * y /
        (2 * Real.pi ^ 2 * W))) *
        (4 * (1 + ell) ^ 2)
  calc
    secondOrderPerronError x (1 + ε) W +
        secondOrderPerronError y (1 + ε) W ≤
      (x ^ (1 + ε) / (2 * Real.pi ^ 2 * W) +
          y ^ (1 + ε) / (2 * Real.pi ^ 2 * W)) *
        ((2 / ε) * (1 + 2 / ε)) := hraw
    _ ≤ (2 * (Real.exp 1 * y /
          (2 * Real.pi ^ 2 * W))) *
        ((2 / ε) * (1 + 2 / ε)) :=
      mul_le_mul_of_nonneg_right hscale hmajor_nonneg
    _ = (2 * (Real.exp 1 * y /
          (2 * Real.pi ^ 2 * W))) *
        ((2 * ell) * (1 + 2 * ell)) := by rw [heps_inv]
    _ ≤ (2 * (Real.exp 1 * y /
          (2 * Real.pi ^ 2 * W))) *
        (4 * (1 + ell) ^ 2) :=
      mul_le_mul_of_nonneg_left hpoly hscale_nonneg

/-- Explicit common Perron-tail budget for the two endpoints `x` and `x+h`
on the moving line based at the upper endpoint. -/
noncomputable def secondOrderMovingEndpointPerronBudget
    (x h W : ℝ) : ℝ :=
  (2 * (Real.exp 1 * (x + h) /
      (2 * Real.pi ^ 2 * W))) *
    (4 * (1 + Real.log (x + h)) ^ 2)

/-- At the selected-height scale `W = T / (2π)`, the moving-endpoint Perron
budget has an exact `T⁻¹` form. -/
theorem secondOrderMovingEndpointPerronBudget_div_two_pi_eq
    {x h T : ℝ} :
    secondOrderMovingEndpointPerronBudget x h (T / (2 * Real.pi)) =
      8 * Real.exp 1 * (x + h) * (1 + Real.log (x + h)) ^ 2 /
        (Real.pi * T) := by
  have hden :
      2 * Real.pi ^ 2 * (T / (2 * Real.pi)) = Real.pi * T := by
    field_simp [Real.pi_ne_zero]
  unfold secondOrderMovingEndpointPerronBudget
  rw [hden]
  ring

/-- Apply the finite-height second-order explicit formula at both endpoints of
one smoothing interval and feed the resulting, genuinely constructed Perron
error bounds into `chebyshevPsi_bounds_of_smoothedApproximation`.

The approximation at each endpoint is the finite residue sum minus the full
second-order contour remainder. No bound on that contour remainder is assumed
or manufactured here. -/
theorem exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : 0 < a)
    (hac : a < c) (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
        (polesY : Finset ℂ) (residueY : ℂ → ℂ),
      (∀ p ∈ polesX,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesX, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ polesX, residueX p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) * (x : ℂ) ^ p / p ^ 2) ∧
      (∀ p ∈ polesY,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesY, p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p ∈ polesY, residueY p =
        if p = 1 then ((x + h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤ secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W ∧
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          chebyshevPsi (x + h) := by
  have hy : 0 < x + h := by linarith
  rcases exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
      hx ha hac hc hW hboundary with
    ⟨polesX, residueX, hpolesX, hclassX, hresidueX, hxError⟩
  rcases exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le
      hy ha hac hc hW hboundary with
    ⟨polesY, residueY, hpolesY, hclassY, hresidueY, hyError⟩
  have hxError' :
      ‖((∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤ secondOrderPerronError x c W := by
    simpa [secondOrderPerronError] using hxError
  have hyError' :
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W := by
    simpa [secondOrderPerronError] using hyError
  let approxX : ℂ :=
    (∑ p ∈ polesX, residueX p) - secondOrderContourRemainder x a c W
  let approxY : ℂ :=
    (∑ p ∈ polesY, residueY p) - secondOrderContourRemainder (x + h) a c W
  let approx : ℝ → ℝ → ℂ := fun u _ => if u = x then approxX else approxY
  let error : ℝ → ℝ → ℝ := fun u _ =>
    if u = x then secondOrderPerronError x c W
    else secondOrderPerronError (x + h) c W
  have hxy : x + h ≠ x := by linarith
  have hbounds := chebyshevPsi_bounds_of_smoothedApproximation
    approx error (T := W) hx hh
    (by simpa [approx, error, approxX] using hxError')
    (by simpa [approx, error, approxY, hxy] using hyError')
  refine ⟨polesX, residueX, polesY, residueY, hpolesX, hclassX, hresidueX,
    hpolesY, hclassY, hresidueY, hxError', hyError', ?_⟩
  simpa [approx, error, approxX, approxY, hxy] using hbounds

/-- Apply the crossing-zero second-order explicit formula at both endpoints of
one smoothing interval and feed the resulting concrete Perron errors into the
Riesz finite-difference sandwich. The finite residue families now include the
origin and retain its derivative coefficient explicitly. -/
theorem exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero
    {x h a c W : ℝ} (hx : 0 < x) (hh : 0 < h) (ha : a < 0)
    (hc : 1 < c) (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
        (polesY : Finset ℂ) (residueY : ℂ → ℂ),
      (∀ p ∈ polesX,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
      residueX 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesX, p ≠ 0 → residueX p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          (x : ℂ) ^ p / p ^ 2) ∧
      (∀ p ∈ polesY,
        a < p.re ∧ p.re < c ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, c]] ×ℂ [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
      residueY 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesY, p ≠ 0 → residueY p =
        if p = 1 then ((x + h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
      ‖((∑ p ∈ polesX, residueX p) -
          secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        secondOrderPerronError x c W ∧
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W ∧
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) ≤
          chebyshevPsi (x + h) := by
  have hy : 0 < x + h := by linarith
  rcases
      exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le_crossing_zero
        hx ha hc hW hboundary with
    ⟨polesX, residueX, hpolesX, hclassX, hcompleteX, hzeroX,
      hresidueX, hxError⟩
  rcases
      exists_norm_residue_sum_sub_contourRemainder_sub_smoothedPsi_le_crossing_zero
        hy ha hc hW hboundary with
    ⟨polesY, residueY, hpolesY, hclassY, hcompleteY, hzeroY,
      hresidueY, hyError⟩
  have hxError' :
      ‖((∑ p ∈ polesX, residueX p) -
          secondOrderContourRemainder x a c W) -
          (smoothedChebyshevPsi x : ℂ)‖ ≤
        secondOrderPerronError x c W := by
    simpa [secondOrderPerronError] using hxError
  have hyError' :
      ‖((∑ p ∈ polesY, residueY p) -
          secondOrderContourRemainder (x + h) a c W) -
          (smoothedChebyshevPsi (x + h) : ℂ)‖ ≤
        secondOrderPerronError (x + h) c W := by
    simpa [secondOrderPerronError] using hyError
  let approxX : ℂ :=
    (∑ p ∈ polesX, residueX p) -
      secondOrderContourRemainder x a c W
  let approxY : ℂ :=
    (∑ p ∈ polesY, residueY p) -
      secondOrderContourRemainder (x + h) a c W
  let approx : ℝ → ℝ → ℂ := fun u _ =>
    if u = x then approxX else approxY
  let error : ℝ → ℝ → ℝ := fun u _ =>
    if u = x then secondOrderPerronError x c W
    else secondOrderPerronError (x + h) c W
  have hxy : x + h ≠ x := by linarith
  have hbounds := chebyshevPsi_bounds_of_smoothedApproximation
    approx error (T := W) hx hh
    (by simpa [approx, error, approxX] using hxError')
    (by simpa [approx, error, approxY, hxy] using hyError')
  refine
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, hzeroX, hresidueX,
      hpolesY, hclassY, hcompleteY, hzeroY, hresidueY,
      hxError', hyError', ?_⟩
  simpa [approx, error, approxX, approxY, hxy] using hbounds

/-- Fully explicit Perron-tail form of the crossing-zero Riesz sandwich. The
right line is chosen as `1 + 1 / log(x+h)`, and the two raw endpoint errors are
replaced by `secondOrderMovingEndpointPerronBudget x h W`. The finite zero sum
and shifted contour remainder remain exact rather than being hidden in the
error term. -/
theorem
    exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero_moving_line
    {x h a W : ℝ} (hx : 1 < x) (hh : 0 < h) (ha : a < 0)
    (hW : 0 < W)
    (hboundary : ∀ p ∈
      ([[a, 1 + 1 / Real.log (x + h)]] ×ℂ
          [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
        a < p.re ∧ p.re < 1 + 1 / Real.log (x + h) ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) :
    ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
        (polesY : Finset ℂ) (residueY : ℂ → ℂ),
      (∀ p ∈ polesX,
        a < p.re ∧ p.re < 1 + 1 / Real.log (x + h) ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, 1 + 1 / Real.log (x + h)]] ×ℂ
            [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
      residueX 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesX, p ≠ 0 → residueX p =
        if p = 1 then (x : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          (x : ℂ) ^ p / p ^ 2) ∧
      (∀ p ∈ polesY,
        a < p.re ∧ p.re < 1 + 1 / Real.log (x + h) ∧
          -(2 * Real.pi * W) < p.im ∧ p.im < 2 * Real.pi * W) ∧
      (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
      (∀ p, p ∈
          ([[a, 1 + 1 / Real.log (x + h)]] ×ℂ
            [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ) →
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
      residueY 0 =
        deriv (fun z : ℂ =>
          -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
      (∀ p ∈ polesY, p ≠ 0 → residueY p =
        if p = 1 then ((x + h : ℝ) : ℂ)
        else -(analyticOrderNatAt riemannZeta p : ℂ) *
          ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a
                  (1 + 1 / Real.log (x + h)) W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a
                  (1 + 1 / Real.log (x + h)) W)).re +
            secondOrderMovingEndpointPerronBudget x h W) /
              Real.log ((x + h) / x) ∧
        ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a
                  (1 + 1 / Real.log (x + h)) W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a
                  (1 + 1 / Real.log (x + h)) W)).re -
            secondOrderMovingEndpointPerronBudget x h W) /
              Real.log ((x + h) / x) ≤
          chebyshevPsi (x + h) := by
  let c : ℝ := 1 + 1 / Real.log (x + h)
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hy : 1 < x + h := by linarith
  have hlogy : 0 < Real.log (x + h) := Real.log_pos hy
  have hc : 1 < c := by
    dsimp [c]
    have : 0 < 1 / Real.log (x + h) := by positivity
    linarith
  rcases
      exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero
        (c := c) hx0 hh ha hc hW (by simpa [c] using hboundary) with
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, hzeroX, hresidueX,
      hpolesY, hclassY, hcompleteY, hzeroY, hresidueY,
      _hxError, _hyError, hbounds⟩
  have herror :
      secondOrderPerronError x c W +
          secondOrderPerronError (x + h) c W ≤
        secondOrderMovingEndpointPerronBudget x h W := by
    simpa [c, secondOrderMovingEndpointPerronBudget] using
      secondOrderPerronError_add_moving_line_le hx hh hW
  have hratio : 1 < (x + h) / x :=
    (lt_div_iff₀ hx0).2 (by linarith)
  have hlog : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  refine
    ⟨polesX, residueX, polesY, residueY,
      ?_, hclassX, ?_, hzeroX, hresidueX,
      ?_, hclassY, ?_, hzeroY, hresidueY, ?_⟩
  · simpa [c] using hpolesX
  · simpa [c] using hcompleteX
  · simpa [c] using hpolesY
  · simpa [c] using hcompleteY
  constructor
  · calc
      chebyshevPsi x ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) :=
        hbounds.1
      _ ≤ ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re +
            secondOrderMovingEndpointPerronBudget x h W) /
              Real.log ((x + h) / x) := by
        apply (div_le_div_iff_of_pos_right hlog).2
        linarith
  · calc
      ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            secondOrderMovingEndpointPerronBudget x h W) /
              Real.log ((x + h) / x) ≤
          ((((∑ p ∈ polesY, residueY p) -
                secondOrderContourRemainder (x + h) a c W) -
              ((∑ p ∈ polesX, residueX p) -
                secondOrderContourRemainder x a c W)).re -
            (secondOrderPerronError x c W +
              secondOrderPerronError (x + h) c W)) /
              Real.log ((x + h) / x) := by
        apply (div_le_div_iff_of_pos_right hlog).2
        linarith
      _ ≤ chebyshevPsi (x + h) :=
        hbounds.2

/-- The second-order Riesz factor gains one power of the logarithmic endpoint
gap.  The smallness hypothesis is the quantitative regime in which
`‖exp z - 1‖ ≤ 2 ‖z‖` applies. -/
theorem norm_secondOrderRieszFactor_sub_le
    {x y : ℝ} {p : ℂ}
    (hx : 0 < x) (hy : 0 < y) (hp : p ≠ 0)
    (hlog : 0 ≤ Real.log y - Real.log x)
    (hsmall : ‖p‖ * (Real.log y - Real.log x) ≤ 1) :
    ‖((y : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2‖ ≤
      2 * x ^ p.re * (Real.log y - Real.log x) / ‖p‖ := by
  let d : ℝ := Real.log y - Real.log x
  have hd : 0 ≤ d := hlog
  have hpNorm : 0 < ‖p‖ := norm_pos_iff.mpr hp
  have hfac :
      (y : ℂ) ^ p - (x : ℂ) ^ p =
        (x : ℂ) ^ p * (Complex.exp ((d : ℂ) * p) - 1) := by
    rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hy.ne'),
      Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hx.ne')]
    rw [← Complex.ofReal_log hy.le, ← Complex.ofReal_log hx.le]
    rw [show (Real.log y : ℂ) * p =
        (Real.log x : ℂ) * p + (d : ℂ) * p by
          simp only [d, Complex.ofReal_sub]
          ring]
    rw [Complex.exp_add]
    ring
  have hzNorm : ‖(d : ℂ) * p‖ = d * ‖p‖ := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  have hzSmall : ‖(d : ℂ) * p‖ ≤ 1 := by
    rw [hzNorm, mul_comm]
    exact hsmall
  have hrem : ‖Complex.exp ((d : ℂ) * p) - 1‖ ≤ 2 * (d * ‖p‖) := by
    simpa [abs_of_nonneg hd] using Complex.norm_exp_sub_one_le hzSmall
  rw [hfac, norm_div, norm_mul, norm_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hx]
  calc
    x ^ p.re * ‖Complex.exp ((d : ℂ) * p) - 1‖ / ‖p‖ ^ 2 ≤
        x ^ p.re * (2 * (d * ‖p‖)) / ‖p‖ ^ 2 := by
      gcongr
    _ = 2 * x ^ p.re * d / ‖p‖ := by
      field_simp [ne_of_gt hpNorm]

/-- Increment form of `norm_secondOrderRieszFactor_sub_le`.  It exposes the
exact smoothing gain `log ((x+h)/x)` used when balancing `h` against a finite
zero height. -/
theorem norm_secondOrderRieszFactor_increment_le
    {x h : ℝ} {p : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h) (hp : p ≠ 0)
    (hsmall : ‖p‖ * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2‖ ≤
      2 * x ^ p.re * Real.log ((x + h) / x) / ‖p‖ := by
  have hy : 0 < x + h := by linarith
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hx).2 (by linarith)
  have hlog : 0 ≤ Real.log (x + h) - Real.log x := by
    rw [← Real.log_div hy.ne' hx.ne']
    exact Real.log_nonneg hratio
  simpa [Real.log_div hy.ne' hx.ne'] using
    norm_secondOrderRieszFactor_sub_le hx hy hp hlog
      (by simpa [Real.log_div hy.ne' hx.ne'] using hsmall)

/-- A uniform finite-height smoothing condition implies the pointwise Riesz
factor bound for every nontrivial zero in the truncation.  The key geometric
input is `‖ρ‖ ≤ T + 1`, obtained from `0 < re ρ < 1` and `|im ρ| ≤ T`. -/
theorem norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset
    {x h T : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h)
    (hρ : ρ ∈ nontrivialZerosFinset T)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
      2 * x ^ ρ.re * Real.log ((x + h) / x) / ‖ρ‖ := by
  rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, him⟩
  have hT : 0 ≤ T := (abs_nonneg ρ.im).trans him
  have hreabs : |ρ.re| < 1 := by
    rw [abs_lt]
    exact ⟨by linarith [hzero.2.1], hzero.2.2⟩
  have hnorm : ‖ρ‖ ≤ T + 1 := by
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ T + 1 := by linarith
  have hlog : 0 ≤ Real.log ((x + h) / x) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hx).2 (by linarith)
  apply norm_secondOrderRieszFactor_increment_le hx hh
  · intro hρ0
    subst ρ
    simpa using hzero.2.1
  · calc
      ‖ρ‖ * Real.log ((x + h) / x) ≤
          (T + 1) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right hnorm hlog
      _ ≤ 1 := hsmall

/-- Under RH, the pointwise Riesz smoothing factor has exact square-root
amplitude at every nontrivial zero in the finite truncation. -/
theorem
    norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ} {ρ : ℂ}
    (hx : 0 < x) (hh : 0 ≤ h)
    (hρ : ρ ∈ nontrivialZerosFinset T)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) / ‖ρ‖ := by
  have hzero := (mem_nontrivialZerosFinset.mp hρ).1
  have hbound :=
    norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset
      hx hh hρ hsmall
  rw [hRH ρ hzero, ← Real.sqrt_eq_rpow] at hbound
  exact hbound

/-- Multiplicity-aware finite-zero version of the smoothing gain.  The
logarithmic endpoint factor remains outside the zero sum, while the remaining
mass is exactly `globalReciprocalZeroMultiplicity`. -/
theorem norm_secondOrderRieszZeroSumWithMultiplicity_increment_le
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  have hlog : 0 ≤ Real.log ((x + h) / x) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ hxpos).2 (by linarith)
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        ∑ ρ ∈ nontrivialZerosFinset T,
          ‖-(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ nontrivialZerosFinset T,
        2 * x * Real.log ((x + h) / x) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hzero := (mem_nontrivialZerosFinset.mp hρ).1
      have hrpow : x ^ ρ.re ≤ x := by
        simpa using
          Real.rpow_le_rpow_of_exponent_le hx hzero.2.2.le
      have hfactor :=
        norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset
          hxpos hh hρ hsmall
      have hmult : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        Nat.cast_nonneg _
      rw [norm_mul, norm_neg, Complex.norm_natCast]
      calc
        (analyticOrderNatAt riemannZeta ρ : ℝ) *
            ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) *
            (2 * x ^ ρ.re * Real.log ((x + h) / x) / ‖ρ‖) :=
          mul_le_mul_of_nonneg_left hfactor hmult
        _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) *
            (2 * x * Real.log ((x + h) / x) / ‖ρ‖) := by
          gcongr
        _ = 2 * x * Real.log ((x + h) / x) *
            ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring
    _ = 2 * x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      unfold ExplicitFormulaAux.globalReciprocalZeroMultiplicity
      rw [Finset.mul_sum]

/-- Under RH, the multiplicity-aware smoothed zero increment has square-root
endpoint scale instead of the unconditional linear scale. -/
theorem norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  have hxpos : 0 < x := zero_lt_one.trans_le hx
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        ∑ ρ ∈ nontrivialZerosFinset T,
          ‖-(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ nontrivialZerosFinset T,
        2 * Real.sqrt x * Real.log ((x + h) / x) *
          ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hfactor :=
        norm_secondOrderRieszFactor_increment_le_of_mem_nontrivialZerosFinset_of_RH
          hRH hxpos hh hρ hsmall
      have hmult : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        Nat.cast_nonneg _
      rw [norm_mul, norm_neg, Complex.norm_natCast]
      calc
        (analyticOrderNatAt riemannZeta ρ : ℝ) *
            ‖(((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2‖ ≤
          (analyticOrderNatAt riemannZeta ρ : ℝ) *
            (2 * Real.sqrt x * Real.log ((x + h) / x) / ‖ρ‖) :=
          mul_le_mul_of_nonneg_left hfactor hmult
        _ = 2 * Real.sqrt x * Real.log ((x + h) / x) *
            ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring
    _ = 2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      unfold ExplicitFormulaAux.globalReciprocalZeroMultiplicity
      rw [Finset.mul_sum]

/-- The global reciprocal zero-mass estimate turns the finite Riesz
difference into an explicit `log² T` budget, uniformly in the endpoints. -/
theorem
    exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        2 * C * x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro x h T hx hh hT hsmall
  have hlog : 0 ≤ Real.log ((x + h) / x) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ (zero_lt_one.trans_le hx)).2 (by linarith)
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
      norm_secondOrderRieszZeroSumWithMultiplicity_increment_le hx hh hsmall
    _ ≤ 2 * x * Real.log ((x + h) / x) *
        (C * (1 + Real.log (T + 6)) ^ 2) := by
      gcongr
      exact hmass T hT
    _ = 2 * C * x * Real.log ((x + h) / x) *
        (1 + Real.log (T + 6)) ^ 2 := by ring

/-- Under RH, the global reciprocal zero-mass estimate gives the smoothed
finite zero increment the expected `sqrt x log² T` scale. -/
theorem
    exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_sqrt_mul_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
        2 * C * Real.sqrt x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hmass⟩
  refine ⟨C, hC, ?_⟩
  intro x h T hx hh hT hsmall
  have hlog : 0 ≤ Real.log ((x + h) / x) := by
    apply Real.log_nonneg
    exact (le_div_iff₀ (zero_lt_one.trans_le hx)).2 (by linarith)
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        -(analyticOrderNatAt riemannZeta ρ : ℂ) *
          ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2)‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
      norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_of_RH
        hRH hx hh hsmall
    _ ≤ 2 * Real.sqrt x * Real.log ((x + h) / x) *
        (C * (1 + Real.log (T + 6)) ^ 2) := by
      gcongr
      exact hmass T hT
    _ = 2 * C * Real.sqrt x * Real.log ((x + h) / x) *
        (1 + Real.log (T + 6)) ^ 2 := by ring

/-- A complete crossing-zero residue family on the strip `-1 < re < c`,
with `c > 1`, consists exactly of `0`, `1`, and the height-`T` nontrivial
zeros. After erasing the two exceptional poles, the support is the canonical
`nontrivialZerosFinset T`. The good-height hypothesis excludes zeros on the
horizontal boundary. -/
theorem erase_zero_one_poles_eq_nontrivialZerosFinset
    {poles : Finset ℂ} {c T : ℝ}
    (hT : 0 < T) (hc : 1 < c)
    (hgood : ExplicitFormulaAux.goodHeight T)
    (hpoles : ∀ p ∈ poles,
      -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T)
    (hclass : ∀ p ∈ poles, p = 0 ∨ p = 1 ∨ riemannZeta p = 0)
    (hcomplete : ∀ p, p ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ) →
      p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ poles) :
    (poles.erase 0).erase 1 = nontrivialZerosFinset T := by
  ext p
  constructor
  · intro hp
    have hp1 : p ≠ 1 := (Finset.mem_erase.mp hp).1
    have hp0data := Finset.mem_erase.mp (Finset.mem_of_mem_erase hp)
    have hp0 : p ≠ 0 := hp0data.1
    have hpP : p ∈ poles := hp0data.2
    have hb := hpoles p hpP
    have hz : riemannZeta p = 0 := by
      rcases hclass p hpP with h | h | h
      · exact (hp0 h).elim
      · exact (hp1 h).elim
      · exact h
    have hnottriv : ∀ n : ℕ, p ≠ -2 * ((n : ℂ) + 1) := by
      intro n hn
      have hre := congrArg Complex.re hn
      norm_num at hre
      have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith [hb.1]
    have hrepos : 0 < p.re := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_re_le_zero
        (le_of_not_gt hnot) hnottriv) hz
    have hrelt : p.re < 1 := by
      by_contra hnot
      exact (riemannZeta_ne_zero_of_one_le_re (le_of_not_gt hnot)) hz
    apply mem_nontrivialZerosFinset.mpr
    refine ⟨⟨hz, hrepos, hrelt⟩, ?_⟩
    rw [abs_le]
    exact ⟨hb.2.2.1.le, hb.2.2.2.le⟩
  · intro hp
    rcases mem_nontrivialZerosFinset.mp hp with ⟨hz, him⟩
    have himne : |p.im| ≠ T := hgood p hz
    have himlt : |p.im| < T := lt_of_le_of_ne him himne
    have himbounds := abs_lt.mp himlt
    have hmemRect :
        p ∈ ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ) := by
      rw [Complex.mem_reProdIm,
        Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ c),
        Set.uIcc_of_le (by linarith : -T ≤ T)]
      exact ⟨⟨by linarith [hz.2.1], by linarith [hz.2.2]⟩,
        ⟨himbounds.1.le, himbounds.2.le⟩⟩
    have hpP : p ∈ poles :=
      hcomplete p hmemRect (Or.inr (Or.inr hz.1))
    apply Finset.mem_erase.mpr
    refine ⟨?_, Finset.mem_erase.mpr ⟨?_, hpP⟩⟩
    · intro hp1
      subst p
      have := hz.2.2
      norm_num at this
    · intro hp0
      subst p
      have := hz.2.1
      norm_num at this

/-- Once the residue support has been identified, the exceptional pole at
`1` separates as the main increment `h`, and every remaining summand is over
the canonical nontrivial-zero truncation. -/
theorem sum_erase_zero_ite_one_eq_main_add_nontrivialZeroSum
    {poles : Finset ℂ} {T h : ℝ} (f : ℂ → ℂ)
    (hone : (1 : ℂ) ∈ poles)
    (hsupport : (poles.erase 0).erase 1 = nontrivialZerosFinset T) :
    (∑ p ∈ poles.erase 0, if p = 1 then (h : ℂ) else f p) =
      (h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ := by
  have honeErase : (1 : ℂ) ∈ poles.erase 0 :=
    Finset.mem_erase.mpr ⟨by norm_num, hone⟩
  have hwithout :
      (∑ p ∈ (poles.erase 0).erase 1,
          if p = 1 then (h : ℂ) else f p) =
        ∑ p ∈ (poles.erase 0).erase 1, f p := by
    apply Finset.sum_congr rfl
    intro p hp
    have hp1 : p ≠ 1 := (Finset.mem_erase.mp hp).1
    simp [hp1]
  calc
    (∑ p ∈ poles.erase 0, if p = 1 then (h : ℂ) else f p) =
        (∑ p ∈ (poles.erase 0).erase 1,
          if p = 1 then (h : ℂ) else f p) +
          (if (1 : ℂ) = 1 then (h : ℂ) else f 1) := by
      exact (Finset.sum_erase_add _ _ honeErase).symm
    _ = (∑ p ∈ (poles.erase 0).erase 1, f p) + (h : ℂ) := by
      rw [hwithout]
      simp
    _ = (h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ := by
      rw [hsupport]
      ring

/-- The selected-good-height budget for the difference of the two shifted
second-order contour remainders on the first negative odd line. -/
noncomputable def secondOrderSelectedHeightContourBudget
    (C x h A T : ℝ) : ℝ :=
  (2 *
        (((C * (x + h) ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2) +
            (C * x ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2)) *
          ((1 + 1 / Real.log (x + h)) - (-1))) +
      (secondOrderOddVerticalBound (x + h) 0 T +
          secondOrderOddVerticalBound x 0 T) *
        (2 * T)) /
    (2 * Real.pi)

/-- Total explicit endpoint budget after adding the common moving-line Perron
tail to the selected-good-height contour-difference budget. -/
noncomputable def secondOrderSelectedHeightTotalBudget
    (C x h A T : ℝ) : ℝ :=
  secondOrderSelectedHeightContourBudget C x h A T +
    secondOrderMovingEndpointPerronBudget x h (T / (2 * Real.pi))

/-- Selected-height contour budget after subtracting both endpoint kernels
before taking norms on all three shifted edges.  Both the horizontal and the
left-vertical contributions retain the logarithmic endpoint gap. -/
noncomputable def secondOrderSelectedHeightIncrementContourBudget
    (C x h A T : ℝ) : ℝ :=
  (2 *
        ((2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
              (1 + Real.log (A + 6)) ^ 2 / T) *
          ((1 + 1 / Real.log (x + h)) - (-1))) +
      (2 * secondOrderOddVerticalBound x 0 T *
          Real.log ((x + h) / x)) *
        (2 * T)) /
    (2 * Real.pi)

/-- Total selected-height budget with horizontal endpoint cancellation and
the same moving-line Perron tail as the original budget. -/
noncomputable def secondOrderSelectedHeightIncrementTotalBudget
    (C x h A T : ℝ) : ℝ :=
  secondOrderSelectedHeightIncrementContourBudget C x h A T +
    secondOrderMovingEndpointPerronBudget x h (T / (2 * Real.pi))

/-- The cancellation-aware selected height controls the actual contour
remainder difference.  This theorem is the analytic consumer of
`secondOrderSelectedHeightIncrementContourBudget`; the budget is not merely a
standalone algebraic definition. -/
theorem
    exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_increment_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            let c := 1 + 1 / Real.log (x + h)
            (∀ p ∈
              ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
                -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T) ∧
            ‖secondOrderContourRemainder (x + h) (-1) c
                  (T / (2 * Real.pi)) -
                secondOrderContourRemainder x (-1) c
                  (T / (2 * Real.pi))‖ ≤
              secondOrderSelectedHeightIncrementContourBudget C x h A T := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderHorizontalXDifference_increment_le
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hhorizontalAll⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxOne : 1 ≤ x :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hypos : 0 < x + h := by linarith
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  let c : ℝ := 1 + 1 / Real.log (x + h)
  have hc : 1 < c := by
    dsimp [c]
    linarith [one_div_pos.mpr hlogpos]
  have hc2 : c ≤ 2 := by
    have hinv : 1 / Real.log (x + h) ≤ 1 :=
      (div_le_one hlogpos).2 hlogOne
    dsimp [c]
    linarith
  let K : ℝ :=
    (2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
      (1 + Real.log (A + 6)) ^ 2 / T) * (c - (-1))
  let L : ℝ :=
    (2 * secondOrderOddVerticalBound x 0 T *
      Real.log ((x + h) / x)) * (2 * T)
  have hhorizontal :
      ∀ t : ℝ, |t| = T →
        ‖secondOrderHorizontalXDifference x (x + h) (-1) c t‖ ≤ K := by
    intro t ht
    simpa [K] using
      hhorizontalAll (x := x) (h := h) (a := -1) (b := c)
        hxOne hh.le (by norm_num) (by linarith) hc2 hsmall t ht
  have hbottom :
      ‖secondOrderHorizontalXDifference x (x + h) (-1) c (-T)‖ ≤ K :=
    hhorizontal (-T) (by rw [abs_neg, abs_of_pos hTpos])
  have htop :
      ‖secondOrderHorizontalXDifference x (x + h) (-1) c T‖ ≤ K :=
    hhorizontal T (abs_of_pos hTpos)
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  have hscale : 2 * Real.pi * (T / (2 * Real.pi)) = T := by
    field_simp [Real.pi_ne_zero]
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hxpos).2 (by linarith)
  have hlogratio : 0 ≤ Real.log ((x + h) / x) :=
    Real.log_nonneg hratio
  have hsmallLeft :
      (1 + T) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (1 + T) * Real.log ((x + h) / x) ≤
          (T + 2) * Real.log ((x + h) / x) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hlogratio
      _ ≤ 1 := hsmall
  have hsmallW :
      (2 * ((0 : ℕ) : ℝ) + 1 +
          2 * Real.pi * (T / (2 * Real.pi))) *
          (Real.log (x + h) - Real.log x) ≤ 1 := by
    rw [hscale, ← Real.log_div hypos.ne' hxpos.ne']
    simpa [add_comm] using hsmallLeft
  have hleft :
      ‖secondOrderLeftXDifference x (x + h) (-1)
          (T / (2 * Real.pi))‖ ≤ L := by
    have hraw := norm_secondOrderLeftXDifference_odd_increment_le_of_pos
      (N := 0) hxpos hypos (by linarith)
        (div_nonneg hTpos.le hden.le) hsmallW
    simpa [hscale, L, ← Real.log_div hypos.ne' hxpos.ne'] using hraw
  have hboundary :
      ∀ p ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ),
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
          -1 < p.re ∧ p.re < c ∧ -T < p.im ∧ p.im < T := by
    simpa using
      (secondOrder_poleCandidate_mem_interior_negativeOdd_rectangle_of_goodHeight
        (N := 0) hTpos hc hgood)
  have hremainder :=
    norm_secondOrderContourRemainder_sub_le_edgeDifferences
      x (x + h) (-1) c (T / (2 * Real.pi))
  rw [hscale] at hremainder
  dsimp only
  refine ⟨hboundary, ?_⟩
  calc
    ‖secondOrderContourRemainder (x + h) (-1) c
          (T / (2 * Real.pi)) -
        secondOrderContourRemainder x (-1) c
          (T / (2 * Real.pi))‖ ≤
        (‖secondOrderHorizontalXDifference x (x + h) (-1) c (-T)‖ +
            ‖secondOrderHorizontalXDifference x (x + h) (-1) c T‖ +
            ‖secondOrderLeftXDifference x (x + h) (-1)
              (T / (2 * Real.pi))‖) /
          (2 * Real.pi) := hremainder
    _ ≤ (K + K + L) / (2 * Real.pi) := by
      exact (div_le_div_iff_of_pos_right hden).2
        (add_le_add (add_le_add hbottom htop) hleft)
    _ = secondOrderSelectedHeightIncrementContourBudget C x h A T := by
      dsimp [K, L, c]
      unfold secondOrderSelectedHeightIncrementContourBudget
      ring

/-- The selected-height contour budget is nonnegative on the parameter range
used by the good-height theorem. -/
theorem secondOrderSelectedHeightContourBudget_nonneg
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤ secondOrderSelectedHeightContourBudget C x h A T := by
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < x + h := by linarith
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  have hlogT : 0 ≤ Real.log (T + 4) :=
    Real.log_nonneg (by linarith)
  have hoddX : 0 ≤ secondOrderOddVerticalBound x 0 T := by
    unfold secondOrderOddVerticalBound
    norm_num
    positivity
  have hoddY : 0 ≤ secondOrderOddVerticalBound (x + h) 0 T := by
    unfold secondOrderOddVerticalBound
    norm_num
    positivity
  have hxterm :
      0 ≤ C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
    positivity
  have hyterm :
      0 ≤ C * (x + h) ^ (2 : ℝ) *
        (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
    positivity
  have hfactor :
      0 ≤ (1 + 1 / Real.log (x + h)) - (-1) := by
    have hinvpos : 0 < 1 / Real.log (x + h) := one_div_pos.mpr hlogpos
    linarith
  unfold secondOrderSelectedHeightContourBudget
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (add_nonneg hyterm hxterm) hfactor))
      (mul_nonneg (add_nonneg hoddY hoddX)
        (mul_nonneg (by norm_num) hTpos.le)))
    (mul_nonneg (by norm_num) Real.pi_pos.le)

/-- The cancellation-aware horizontal scalar is no larger than the sum of
the two separate endpoint scalars in the small-increment regime. -/
lemma secondOrderIncrementHorizontalScalar_le_separateEndpoints
    {x h T : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hT : 0 < T)
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) / T ≤
      ((x + h) ^ (2 : ℝ) + x ^ (2 : ℝ)) / T ^ 2 := by
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hx).2 (by linarith)
  have hd : 0 ≤ Real.log ((x + h) / x) :=
    Real.log_nonneg hratio
  have hTd :
      T * Real.log ((x + h) / x) ≤ 1 := by
    calc
      T * Real.log ((x + h) / x) ≤
          (T + 2) * Real.log ((x + h) / x) := by
        nlinarith
      _ ≤ 1 := hsmall
  have hxy2 :
      x ^ (2 : ℝ) ≤ (x + h) ^ (2 : ℝ) :=
    Real.rpow_le_rpow hx.le (by linarith) (by norm_num)
  have hx2nonneg : 0 ≤ x ^ (2 : ℝ) :=
    Real.rpow_nonneg hx.le _
  have hmain :
      2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) * T ≤
        (x + h) ^ (2 : ℝ) + x ^ (2 : ℝ) := by
    have hscaled :
        x ^ (2 : ℝ) *
            (T * Real.log ((x + h) / x)) ≤ x ^ (2 : ℝ) := by
      simpa using mul_le_mul_of_nonneg_left hTd hx2nonneg
    nlinarith
  rw [div_le_div_iff₀ hT (sq_pos_of_pos hT)]
  rw [show T ^ 2 = T * T by ring]
  convert mul_le_mul_of_nonneg_right hmain hT.le using 1 <;> ring

/-- For a genuine positive increment, the cancellation-aware horizontal
scalar is strictly smaller than the separate-endpoint scalar. -/
lemma secondOrderIncrementHorizontalScalar_lt_separateEndpoints
    {x h T : ℝ} (hx : 0 < x) (hh : 0 < h) (hT : 0 < T)
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) / T <
      ((x + h) ^ (2 : ℝ) + x ^ (2 : ℝ)) / T ^ 2 := by
  have hratio : 1 < (x + h) / x :=
    (lt_div_iff₀ hx).2 (by linarith)
  have hd : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hTd :
      T * Real.log ((x + h) / x) < 1 := by
    calc
      T * Real.log ((x + h) / x) <
          (T + 2) * Real.log ((x + h) / x) := by
        nlinarith
      _ ≤ 1 := hsmall
  have hxy2 :
      x ^ (2 : ℝ) < (x + h) ^ (2 : ℝ) :=
    Real.rpow_lt_rpow hx.le (by linarith) (by norm_num)
  have hx2pos : 0 < x ^ (2 : ℝ) :=
    Real.rpow_pos_of_pos hx _
  have hmain :
      2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) * T <
        (x + h) ^ (2 : ℝ) + x ^ (2 : ℝ) := by
    have hscaled :
        x ^ (2 : ℝ) *
            (T * Real.log ((x + h) / x)) < x ^ (2 : ℝ) := by
      simpa using mul_lt_mul_of_pos_left hTd hx2pos
    nlinarith
  rw [div_lt_div_iff₀ hT (sq_pos_of_pos hT)]
  rw [show T ^ 2 = T * T by ring]
  convert mul_lt_mul_of_pos_right hmain hT using 1 <;> ring

/-- On the selected `N = 0` left vertical line, endpoint cancellation also
improves the scalar before multiplication by the edge length. -/
lemma secondOrderIncrementLeftVerticalScalar_le_separateEndpoints
    {x h T : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hT : 0 < T)
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    2 * secondOrderOddVerticalBound x 0 T *
        Real.log ((x + h) / x) ≤
      secondOrderOddVerticalBound (x + h) 0 T +
        secondOrderOddVerticalBound x 0 T := by
  have hypos : 0 < x + h := by linarith
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hx).2 (by linarith)
  have hd : 0 ≤ Real.log ((x + h) / x) :=
    Real.log_nonneg hratio
  have htwod : 2 * Real.log ((x + h) / x) ≤ 1 := by
    calc
      2 * Real.log ((x + h) / x) ≤
          (T + 2) * Real.log ((x + h) / x) := by
        exact mul_le_mul_of_nonneg_right (by linarith) hd
      _ ≤ 1 := hsmall
  have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  have hlogT : 0 ≤ Real.log (T + 4) :=
    Real.log_nonneg (by linarith)
  have hoddX : 0 ≤ secondOrderOddVerticalBound x 0 T := by
    unfold secondOrderOddVerticalBound
    norm_num
    positivity
  have hoddY : 0 ≤ secondOrderOddVerticalBound (x + h) 0 T := by
    unfold secondOrderOddVerticalBound
    norm_num
    positivity
  have hscaled :
      2 * secondOrderOddVerticalBound x 0 T *
          Real.log ((x + h) / x) ≤
        secondOrderOddVerticalBound x 0 T := by
    calc
      2 * secondOrderOddVerticalBound x 0 T *
            Real.log ((x + h) / x) =
          secondOrderOddVerticalBound x 0 T *
            (2 * Real.log ((x + h) / x)) := by ring
      _ ≤ secondOrderOddVerticalBound x 0 T * 1 :=
        mul_le_mul_of_nonneg_left htwod hoddX
      _ = secondOrderOddVerticalBound x 0 T := by ring
  linarith

/-- The cancellation-aware contour budget is nonnegative on the selected
height parameter range. -/
theorem secondOrderSelectedHeightIncrementContourBudget_nonneg
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤ secondOrderSelectedHeightIncrementContourBudget C x h A T := by
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < x + h := by linarith
  have hratio : 1 ≤ (x + h) / x :=
    (le_div_iff₀ hxpos).2 (by linarith)
  have hlogratio : 0 ≤ Real.log ((x + h) / x) :=
    Real.log_nonneg hratio
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  have hfactor :
      0 ≤ (1 + 1 / Real.log (x + h)) - (-1) := by
    linarith [one_div_pos.mpr hlogpos]
  have hseries : 0 ≤ vonMangoldtLSeriesNorm 1 :=
    tsum_nonneg fun n => norm_nonneg _
  have hlogT : 0 ≤ Real.log (T + 4) :=
    Real.log_nonneg (by linarith)
  have hoddX : 0 ≤ secondOrderOddVerticalBound x 0 T := by
    unfold secondOrderOddVerticalBound
    norm_num
    positivity
  unfold secondOrderSelectedHeightIncrementContourBudget
  exact div_nonneg
    (add_nonneg
      (mul_nonneg (by norm_num)
        (mul_nonneg (by positivity) hfactor))
      (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) hoddX) hlogratio)
        (mul_nonneg (by norm_num) hTpos.le)))
    (mul_nonneg (by norm_num) Real.pi_pos.le)

/-- In the small-increment regime, cancellation never enlarges the selected
height contour budget relative to separate endpoint estimates. -/
theorem secondOrderSelectedHeightIncrementContourBudget_le
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    secondOrderSelectedHeightIncrementContourBudget C x h A T ≤
      secondOrderSelectedHeightContourBudget C x h A T := by
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < x + h := by linarith
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  have hfactor :
      0 ≤ (1 + 1 / Real.log (x + h)) - (-1) := by
    linarith [one_div_pos.mpr hlogpos]
  have hscalar :=
    secondOrderIncrementHorizontalScalar_le_separateEndpoints
      hxpos hh.le hTpos hsmall
  have hweight :
      0 ≤ C * (1 + Real.log (A + 6)) ^ 2 :=
    mul_nonneg hC (sq_nonneg _)
  have hhorizontal :
      2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
            (1 + Real.log (A + 6)) ^ 2 / T ≤
        C * (x + h) ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 +
          C * x ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
    calc
      2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
            (1 + Real.log (A + 6)) ^ 2 / T =
          (C * (1 + Real.log (A + 6)) ^ 2) *
            (2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) / T) := by
        ring
      _ ≤ (C * (1 + Real.log (A + 6)) ^ 2) *
            (((x + h) ^ (2 : ℝ) + x ^ (2 : ℝ)) / T ^ 2) :=
        mul_le_mul_of_nonneg_left hscalar hweight
      _ = C * (x + h) ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 +
          C * x ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
        ring
  unfold secondOrderSelectedHeightIncrementContourBudget
    secondOrderSelectedHeightContourBudget
  gcongr
  exact secondOrderIncrementLeftVerticalScalar_le_separateEndpoints
    hxpos hh.le hTpos hsmall

/-- If the selected log-derivative constant is positive, a genuine endpoint
increment makes the cancellation-aware contour budget strictly smaller. -/
theorem secondOrderSelectedHeightIncrementContourBudget_lt
    {C x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    secondOrderSelectedHeightIncrementContourBudget C x h A T <
      secondOrderSelectedHeightContourBudget C x h A T := by
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < x + h := by linarith
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  have hfactor :
      0 < (1 + 1 / Real.log (x + h)) - (-1) := by
    linarith [one_div_pos.mpr hlogpos]
  have hlogA : 0 ≤ Real.log (A + 6) :=
    Real.log_nonneg (by linarith)
  have hweight :
      0 < C * (1 + Real.log (A + 6)) ^ 2 := by
    positivity
  have hscalar :=
    secondOrderIncrementHorizontalScalar_lt_separateEndpoints
      hxpos hh hTpos hsmall
  have hhorizontal :
      2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
            (1 + Real.log (A + 6)) ^ 2 / T <
        C * (x + h) ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 +
          C * x ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
    calc
      2 * C * x ^ (2 : ℝ) * Real.log ((x + h) / x) *
            (1 + Real.log (A + 6)) ^ 2 / T =
          (C * (1 + Real.log (A + 6)) ^ 2) *
            (2 * x ^ (2 : ℝ) * Real.log ((x + h) / x) / T) := by
        ring
      _ < (C * (1 + Real.log (A + 6)) ^ 2) *
            (((x + h) ^ (2 : ℝ) + x ^ (2 : ℝ)) / T ^ 2) :=
        mul_lt_mul_of_pos_left hscalar hweight
      _ = C * (x + h) ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 +
          C * x ^ (2 : ℝ) *
              (1 + Real.log (A + 6)) ^ 2 / T ^ 2 := by
        ring
  have hverticalScalar :=
    secondOrderIncrementLeftVerticalScalar_le_separateEndpoints
      hxpos hh.le hTpos hsmall
  have hvertical :
      (2 * secondOrderOddVerticalBound x 0 T *
            Real.log ((x + h) / x)) * (2 * T) ≤
        (secondOrderOddVerticalBound (x + h) 0 T +
            secondOrderOddVerticalBound x 0 T) * (2 * T) :=
    mul_le_mul_of_nonneg_right hverticalScalar (by positivity)
  unfold secondOrderSelectedHeightIncrementContourBudget
    secondOrderSelectedHeightContourBudget
  have hden : 0 < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
  apply (div_lt_div_iff_of_pos_right hden).2
  have hscaled := mul_lt_mul_of_pos_right hhorizontal hfactor
  nlinarith [hvertical]

/-- The cancellation-aware total budget is nonnegative. -/
theorem secondOrderSelectedHeightIncrementTotalBudget_nonneg
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤ secondOrderSelectedHeightIncrementTotalBudget C x h A T := by
  rw [secondOrderSelectedHeightIncrementTotalBudget,
    secondOrderMovingEndpointPerronBudget_div_two_pi_eq]
  exact add_nonneg
    (secondOrderSelectedHeightIncrementContourBudget_nonneg hC hx hh hA hT)
    (by
      have hTpos : 0 < T := by linarith [hT.1]
      have hypos : 0 < x + h := by
        have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
        linarith
      positivity)

/-- The same Perron tail is added to both budgets, so the horizontal
cancellation comparison propagates to the total selected-height budget. -/
theorem secondOrderSelectedHeightIncrementTotalBudget_le
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    secondOrderSelectedHeightIncrementTotalBudget C x h A T ≤
      secondOrderSelectedHeightTotalBudget C x h A T := by
  unfold secondOrderSelectedHeightIncrementTotalBudget
    secondOrderSelectedHeightTotalBudget
  exact add_le_add
    (secondOrderSelectedHeightIncrementContourBudget_le
      hC hx hh hA hT hsmall) le_rfl

/-- Under the same nondegenerate hypotheses, the total budget also decreases
strictly because its Perron summand is unchanged. -/
theorem secondOrderSelectedHeightIncrementTotalBudget_lt
    {C x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    secondOrderSelectedHeightIncrementTotalBudget C x h A T <
      secondOrderSelectedHeightTotalBudget C x h A T := by
  unfold secondOrderSelectedHeightIncrementTotalBudget
    secondOrderSelectedHeightTotalBudget
  simpa [add_comm] using
    add_lt_add_right
      (secondOrderSelectedHeightIncrementContourBudget_lt
        hC hx hh hA hT hsmall)
      (secondOrderMovingEndpointPerronBudget x h (T / (2 * Real.pi)))

/-- The selected-height contour budget splits into an explicit horizontal
`T⁻²` term and the original `N = 0` left-vertical `T` term.  Keeping the latter
unsimplified preserves its reciprocal endpoint powers for later optimization.
-/
theorem secondOrderSelectedHeightContourBudget_le_explicit
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    secondOrderSelectedHeightContourBudget C x h A T ≤
      6 * C * (x + h) ^ (2 : ℝ) *
          (1 + Real.log (A + 6)) ^ 2 / (Real.pi * T ^ 2) +
        (secondOrderOddVerticalBound (x + h) 0 T +
            secondOrderOddVerticalBound x 0 T) *
          T / Real.pi := by
  let y : ℝ := x + h
  let K : ℝ :=
    C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  let Hsum : ℝ :=
    C * y ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2 +
      C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2
  let H : ℝ := Hsum * ((1 + 1 / Real.log y) - (-1))
  let V : ℝ :=
    secondOrderOddVerticalBound y 0 T +
      secondOrderOddVerticalBound x 0 T
  have hTpos : 0 < T := by linarith [hT.1]
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < y := by dsimp [y]; linarith
  have hxy : x ≤ y := by dsimp [y]; linarith
  have hlogOne : 1 ≤ Real.log y :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans hxy)
  have hlogpos : 0 < Real.log y := zero_lt_one.trans_le hlogOne
  have hfactor_nonneg : 0 ≤ (1 + 1 / Real.log y) - (-1) := by
    have hinvpos : 0 < 1 / Real.log y := one_div_pos.mpr hlogpos
    linarith
  have hfactor_le : (1 + 1 / Real.log y) - (-1) ≤ 3 := by
    have hinv : 1 / Real.log y ≤ 1 :=
      (div_le_one hlogpos).2 hlogOne
    linarith
  have hxpow :
      x ^ (2 : ℝ) ≤ y ^ (2 : ℝ) :=
    Real.rpow_le_rpow hxpos.le hxy (by norm_num)
  have hxterm :
      C * x ^ (2 : ℝ) * (1 + Real.log (A + 6)) ^ 2 / T ^ 2 ≤ K := by
    dsimp [K]
    gcongr
  have hK : 0 ≤ K := by
    dsimp [K]
    positivity
  have hsum_nonneg : 0 ≤ Hsum := by
    dsimp [Hsum]
    positivity
  have hsum_le : Hsum ≤ 2 * K := by
    dsimp [Hsum, K] at *
    nlinarith
  have hhorizontal : H ≤ 6 * K := by
    dsimp [H]
    calc
      Hsum * ((1 + 1 / Real.log y) - (-1)) ≤
          (2 * K) * 3 :=
        mul_le_mul hsum_le hfactor_le hfactor_nonneg
          (mul_nonneg (by norm_num) hK)
      _ = 6 * K := by ring
  calc
    secondOrderSelectedHeightContourBudget C x h A T =
        H / Real.pi + V * T / Real.pi := by
      unfold secondOrderSelectedHeightContourBudget
      dsimp [H, Hsum, V, y]
      ring
    _ ≤ (6 * K) / Real.pi + V * T / Real.pi :=
      add_le_add
        (div_le_div_of_nonneg_right hhorizontal Real.pi_pos.le)
        le_rfl
    _ = 6 * C * (x + h) ^ (2 : ℝ) *
          (1 + Real.log (A + 6)) ^ 2 / (Real.pi * T ^ 2) +
        (secondOrderOddVerticalBound (x + h) 0 T +
            secondOrderOddVerticalBound x 0 T) *
          T / Real.pi := by
      dsimp [K, V, y]
      ring

/-- The full selected-height budget is nonnegative on the same admissible
parameter range. -/
theorem secondOrderSelectedHeightTotalBudget_nonneg
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    0 ≤ secondOrderSelectedHeightTotalBudget C x h A T := by
  rw [secondOrderSelectedHeightTotalBudget,
    secondOrderMovingEndpointPerronBudget_div_two_pi_eq]
  exact add_nonneg
    (secondOrderSelectedHeightContourBudget_nonneg hC hx hh hA hT)
    (by
      have hTpos : 0 < T := by linarith [hT.1]
      have hypos : 0 < x + h := by
        have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
        linarith
      positivity)

/-- Explicit componentwise upper bound for the selected-height total budget:
horizontal contour decay is `T⁻²`, the moving Perron tail is exactly `T⁻¹`,
and the `N = 0` left-vertical term remains visible as a separate summand. -/
theorem secondOrderSelectedHeightTotalBudget_le_explicit
    {C x h A T : ℝ}
    (hC : 0 ≤ C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1)) :
    secondOrderSelectedHeightTotalBudget C x h A T ≤
      6 * C * (x + h) ^ (2 : ℝ) *
          (1 + Real.log (A + 6)) ^ 2 / (Real.pi * T ^ 2) +
        (secondOrderOddVerticalBound (x + h) 0 T +
            secondOrderOddVerticalBound x 0 T) *
          T / Real.pi +
        8 * Real.exp 1 * (x + h) * (1 + Real.log (x + h)) ^ 2 /
          (Real.pi * T) := by
  rw [secondOrderSelectedHeightTotalBudget,
    secondOrderMovingEndpointPerronBudget_div_two_pi_eq]
  exact add_le_add
    (secondOrderSelectedHeightContourBudget_le_explicit hC hx hh hA hT)
    le_rfl

/-- On every unit height interval above `4`, select a genuine good height and
combine the crossing-zero residue formula, the three-edge contour estimate on
`Re(s) = -1`, the moving Perron line, and the Riesz sandwich.

The only analytic terms left in the displayed endpoint bounds are the actual
finite residue sums and `secondOrderSelectedHeightTotalBudget`. Pole
classification, rectangle completeness, and analytic multiplicities remain
public so that downstream zero-sum estimates can consume this theorem. -/
theorem
    exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
              (polesY : Finset ℂ) (residueY : ℂ → ℂ),
            (∀ p ∈ polesX,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
            residueX 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesX, p ≠ 0 → residueX p =
              if p = 1 then (x : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                (x : ℂ) ^ p / p ^ 2) ∧
            (∀ p ∈ polesY,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
            residueY 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesY, p ≠ 0 → residueY p =
              if p = 1 then ((x + h : ℝ) : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
            polesX = polesY ∧
            (∑ p ∈ polesY, residueY p) -
                (∑ p ∈ polesX, residueX p) =
              (deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z *
                    ((x + h : ℝ) : ℂ) ^ z) 0 -
                deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
                (∑ p ∈ polesX.erase 0,
                  (if p = 1 then (h : ℂ)
                  else -(analyticOrderNatAt riemannZeta p : ℂ) *
                    (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2)) ∧
            chebyshevPsi x ≤
                (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re +
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ∧
              (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re -
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_sub_neg_one_le
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hremainderAll⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh
  have hexpOne : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hx1 : 1 < x := hexpOne.trans_le hx
  have hxOne : 1 ≤ x := hx1.le
  have hy1 : 1 < x + h := by linarith
  have hyOne : 1 ≤ x + h := hy1.le
  have hypos : 0 < x + h := zero_lt_one.trans hy1
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  let c : ℝ := 1 + 1 / Real.log (x + h)
  have hc : 1 < c := by
    dsimp [c]
    linarith [one_div_pos.mpr hlogpos]
  have hc2 : c ≤ 2 := by
    have hinv : 1 / Real.log (x + h) ≤ 1 :=
      (div_le_one hlogpos).2 hlogOne
    dsimp [c]
    linarith
  rcases hremainderAll hxOne hyOne hc hc2 with
    ⟨hboundary, hremainder⟩
  have hTpos : 0 < T := by linarith [hT.1]
  let W : ℝ := T / (2 * Real.pi)
  have hW : 0 < W := by
    dsimp [W]
    positivity
  have hscale : 2 * Real.pi * W = T := by
    dsimp [W]
    field_simp [Real.pi_ne_zero]
  have hboundaryW :
      ∀ p ∈
        ([[(-1 : ℝ), c]] ×ℂ
          [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
          -1 < p.re ∧ p.re < c ∧
            -(2 * Real.pi * W) < p.im ∧
              p.im < 2 * Real.pi * W := by
    simpa [hscale] using hboundary
  rcases
      exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero_moving_line
        (a := -1) (W := W) hx1 hh (by norm_num) hW
          (by simpa [c] using hboundaryW) with
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, hzeroX, hresidueX,
      hpolesY, hclassY, hcompleteY, hzeroY, hresidueY, hbounds⟩
  let RX : ℂ := secondOrderContourRemainder x (-1) c W
  let RY : ℂ := secondOrderContourRemainder (x + h) (-1) c W
  let SX : ℂ := ∑ p ∈ polesX, residueX p
  let SY : ℂ := ∑ p ∈ polesY, residueY p
  let BC : ℝ := secondOrderSelectedHeightContourBudget C x h A T
  let BP : ℝ :=
    secondOrderMovingEndpointPerronBudget x h W
  have hremainder' : ‖RY - RX‖ ≤ BC := by
    simpa [RX, RY, BC, W, c, hscale,
      secondOrderSelectedHeightContourBudget] using hremainder
  have hremainderRe : |(RY - RX).re| ≤ BC :=
    (abs_re_le_norm (RY - RX)).trans hremainder'
  rcases abs_le.mp hremainderRe with ⟨hremainderLower, hremainderUpper⟩
  have hbounds' :
      chebyshevPsi x ≤
          (((SY - RY) - (SX - RX)).re + BP) /
            Real.log ((x + h) / x) ∧
        (((SY - RY) - (SX - RX)).re - BP) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) := by
    simpa [SX, SY, RX, RY, BP, c, W] using hbounds
  have hdecomp :
      ((SY - RY) - (SX - RX)).re =
        (SY - SX).re - (RY - RX).re := by
    simp
    ring
  have htotal :
      secondOrderSelectedHeightTotalBudget C x h A T = BC + BP := by
    rfl
  have hratio : 1 < (x + h) / x :=
    (lt_div_iff₀ (zero_lt_one.trans hx1)).2 (by linarith)
  have hlogratio : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hpolesEq : polesX = polesY := by
    ext p
    constructor
    · intro hp
      have hpBounds := hpolesX p hp
      apply hcompleteY p
      · rw [Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
            1 + 1 / Real.log (x + h)),
          Set.uIcc_of_le (by linarith [hW] :
            -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
        exact
          ⟨⟨hpBounds.1.le, hpBounds.2.1.le⟩,
            ⟨hpBounds.2.2.1.le, hpBounds.2.2.2.le⟩⟩
      · exact hclassX p hp
    · intro hp
      have hpBounds := hpolesY p hp
      apply hcompleteX p
      · rw [Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
            1 + 1 / Real.log (x + h)),
          Set.uIcc_of_le (by linarith [hW] :
            -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
        exact
          ⟨⟨hpBounds.1.le, hpBounds.2.1.le⟩,
            ⟨hpBounds.2.2.1.le, hpBounds.2.2.2.le⟩⟩
      · exact hclassY p hp
  subst polesY
  have hzeroMem : 0 ∈ polesX := by
    apply hcompleteX 0
    · rw [Complex.mem_reProdIm,
        Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
          1 + 1 / Real.log (x + h)),
        Set.uIcc_of_le (by linarith [hW] :
          -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
      simp only [Complex.zero_re, Complex.zero_im, Set.mem_Icc]
      constructor
      · constructor <;> linarith
      · constructor <;> nlinarith [Real.pi_pos]
    · exact Or.inl rfl
  have hsumDiff :
      (∑ p ∈ polesX, residueY p) -
          (∑ p ∈ polesX, residueX p) =
        (deriv (fun z : ℂ =>
            -logDeriv riemannZeta z *
              ((x + h : ℝ) : ℂ) ^ z) 0 -
          deriv (fun z : ℂ =>
            -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
          ∑ p ∈ polesX.erase 0,
            if p = 1 then (h : ℂ)
            else -(analyticOrderNatAt riemannZeta p : ℂ) *
              (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2 := by
    rw [show (∑ p ∈ polesX, residueY p) =
        (∑ p ∈ polesX.erase 0, residueY p) + residueY 0 by
          exact (Finset.sum_erase_add _ _ hzeroMem).symm]
    rw [show (∑ p ∈ polesX, residueX p) =
        (∑ p ∈ polesX.erase 0, residueX p) + residueX 0 by
          exact (Finset.sum_erase_add _ _ hzeroMem).symm]
    rw [hzeroY, hzeroX]
    rw [show
        (∑ p ∈ polesX.erase 0, residueY p) +
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 -
            ((∑ p ∈ polesX.erase 0, residueX p) +
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) =
          (deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 -
            deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
            ((∑ p ∈ polesX.erase 0, residueY p) -
              (∑ p ∈ polesX.erase 0, residueX p)) by ring]
    rw [← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hpMem : p ∈ polesX := Finset.mem_of_mem_erase hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    rw [hresidueY p hpMem hp0, hresidueX p hpMem hp0]
    split_ifs with hp1
    · subst p
      norm_num
    · ring
  refine ⟨polesX, residueX, polesX, residueY,
    ?_, hclassX, ?_, hzeroX, hresidueX,
    ?_, hclassY, ?_, hzeroY, hresidueY, rfl, hsumDiff, ?_⟩
  · simpa [c, hscale] using hpolesX
  · simpa [c, hscale] using hcompleteX
  · simpa [c, hscale] using hpolesY
  · simpa [c, hscale] using hcompleteY
  constructor
  · calc
      chebyshevPsi x ≤
          (((SY - RY) - (SX - RX)).re + BP) /
            Real.log ((x + h) / x) := hbounds'.1
      _ ≤ ((SY - SX).re +
            secondOrderSelectedHeightTotalBudget C x h A T) /
          Real.log ((x + h) / x) := by
        apply (div_le_div_iff_of_pos_right hlogratio).2
        rw [hdecomp]
        rw [htotal]
        linarith
  · calc
      ((SY - SX).re -
            secondOrderSelectedHeightTotalBudget C x h A T) /
          Real.log ((x + h) / x) ≤
          (((SY - RY) - (SX - RX)).re - BP) /
            Real.log ((x + h) / x) := by
        apply (div_le_div_iff_of_pos_right hlogratio).2
        rw [hdecomp]
        rw [htotal]
        linarith
      _ ≤ chebyshevPsi (x + h) := hbounds'.2

/-- Endpoint-specialized compatibility form of the uniform crossing-zero
selected-height sandwich. -/
theorem
    exists_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one
    {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∃ (polesX : Finset ℂ) (residueX : ℂ → ℂ)
              (polesY : Finset ℂ) (residueY : ℂ → ℂ),
            (∀ p ∈ polesX,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesX, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesX) ∧
            residueX 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesX, p ≠ 0 → residueX p =
              if p = 1 then (x : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                (x : ℂ) ^ p / p ^ 2) ∧
            (∀ p ∈ polesY,
              -1 < p.re ∧
                p.re < 1 + 1 / Real.log (x + h) ∧
                -T < p.im ∧ p.im < T) ∧
            (∀ p ∈ polesY, p = 0 ∨ p = 1 ∨ riemannZeta p = 0) ∧
            (∀ p, p ∈
                ([[(-1 : ℝ), 1 + 1 / Real.log (x + h)]] ×ℂ
                  [[-T, T]] : Set ℂ) →
              p = 0 ∨ p = 1 ∨ riemannZeta p = 0 → p ∈ polesY) ∧
            residueY 0 =
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 ∧
            (∀ p ∈ polesY, p ≠ 0 → residueY p =
              if p = 1 then ((x + h : ℝ) : ℂ)
              else -(analyticOrderNatAt riemannZeta p : ℂ) *
                ((x + h : ℝ) : ℂ) ^ p / p ^ 2) ∧
            polesX = polesY ∧
            (∑ p ∈ polesY, residueY p) -
                (∑ p ∈ polesX, residueX p) =
              (deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z *
                    ((x + h : ℝ) : ℂ) ^ z) 0 -
                deriv (fun z : ℂ =>
                  -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
                (∑ p ∈ polesX.erase 0,
                  (if p = 1 then (h : ℂ)
                  else -(analyticOrderNatAt riemannZeta p : ℂ) *
                    (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2)) ∧
            chebyshevPsi x ≤
                (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re +
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ∧
              (((∑ p ∈ polesY, residueY p) -
                    (∑ p ∈ polesX, residueX p)).re -
                  secondOrderSelectedHeightTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨T, hT, hgood, hbound hx hh⟩

/-- The contribution of the double pole at the origin to one smoothed
endpoint increment. -/
noncomputable def secondOrderOriginDerivativeIncrement
    (x h : ℝ) : ℂ :=
  deriv (fun z : ℂ =>
      -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 -
    deriv (fun z : ℂ =>
      -logDeriv riemannZeta z * (x : ℂ) ^ z) 0

/-- The double-pole contribution at the origin is elementary after taking
the endpoint difference: the derivative of `-ζ'/ζ` cancels, leaving its
value `-log (2π)` times the logarithmic endpoint increment. -/
theorem secondOrderOriginDerivativeIncrement_eq
    {x h : ℝ} (hx : 0 < x) (hy : 0 < x + h) :
    secondOrderOriginDerivativeIncrement x h =
      -(Real.log (2 * Real.pi) : ℂ) *
        (Real.log ((x + h) / x) : ℂ) := by
  have hzeta0 : riemannZeta (0 : ℂ) ≠ 0 := by
    rw [riemannZeta_zero]
    norm_num
  have hlog :
      DifferentiableAt ℂ (fun z : ℂ => -logDeriv riemannZeta z) 0 :=
    (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      0 (by norm_num) hzeta0).neg.differentiableAt
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx.ne'
  have hy0 : ((x + h : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hy.ne'
  have hpowX : DifferentiableAt ℂ (fun z : ℂ => (x : ℂ) ^ z) 0 :=
    (differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) 0).const_cpow
      (Or.inl hx0)
  have hpowY :
      DifferentiableAt ℂ (fun z : ℂ => ((x + h : ℝ) : ℂ) ^ z) 0 :=
    (differentiableAt_id : DifferentiableAt ℂ (fun z : ℂ => z) 0).const_cpow
      (Or.inl hy0)
  have hlogValue :
      logDeriv riemannZeta 0 = (Real.log (2 * Real.pi) : ℂ) := by
    simpa only [logDeriv_apply] using
      deriv_riemannZeta_zero_div_riemannZeta_zero
  have hlogX :
      Complex.log (x : ℂ) = (Real.log x : ℂ) := by
    rw [Complex.ofReal_log hx.le]
  have hlogY :
      Complex.log ((x + h : ℝ) : ℂ) =
        (Real.log (x + h) : ℂ) := by
    rw [Complex.ofReal_log hy.le]
  have hid :
      DifferentiableAt ℂ (fun z : ℂ => z) 0 :=
    differentiableAt_id
  have hderivX :
      deriv (fun z : ℂ => (x : ℂ) ^ z) 0 = Complex.log (x : ℂ) := by
    simpa using Complex.deriv_const_cpow hid (x : ℂ)
  have hderivY :
      deriv (fun z : ℂ => ((x + h : ℝ) : ℂ) ^ z) 0 =
        Complex.log ((x + h : ℝ) : ℂ) := by
    simpa using Complex.deriv_const_cpow hid ((x + h : ℝ) : ℂ)
  unfold secondOrderOriginDerivativeIncrement
  change
    deriv ((fun z : ℂ => -logDeriv riemannZeta z) *
        (fun z : ℂ => ((x + h : ℝ) : ℂ) ^ z)) 0 -
      deriv ((fun z : ℂ => -logDeriv riemannZeta z) *
        (fun z : ℂ => (x : ℂ) ^ z)) 0 = _
  rw [deriv_mul hlog hpowY, deriv_mul hlog hpowX, hderivY, hderivX]
  simp only [cpow_zero, mul_one, hlogValue, hlogX, hlogY]
  rw [Real.log_div hy.ne' hx.ne']
  push_cast
  ring

/-- The multiplicity-aware nontrivial-zero contribution to one second-order
Riesz endpoint increment. -/
noncomputable def secondOrderNontrivialZeroIncrement
    (x h T : ℝ) : ℂ :=
  ∑ ρ ∈ nontrivialZerosFinset T,
    -(analyticOrderNatAt riemannZeta ρ : ℂ) *
      (((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2

/-- The standardized nontrivial-zero increment inherits the finite
multiplicity-aware smoothing estimate. -/
theorem norm_secondOrderNontrivialZeroIncrement_le
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
      2 * x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  have hsum :
      secondOrderNontrivialZeroIncrement x h T =
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2) := by
    unfold secondOrderNontrivialZeroIncrement
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hsum]
  exact norm_secondOrderRieszZeroSumWithMultiplicity_increment_le
    hx hh hsmall

/-- Standardized form of the RH square-root bound for the smoothed
nontrivial-zero increment. -/
theorem norm_secondOrderNontrivialZeroIncrement_le_of_RH
    (hRH : RiemannHypothesis.Statement)
    {x h T : ℝ}
    (hx : 1 ≤ x) (hh : 0 ≤ h)
    (hsmall : (T + 1) * Real.log ((x + h) / x) ≤ 1) :
    ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
      2 * Real.sqrt x * Real.log ((x + h) / x) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  have hsum :
      secondOrderNontrivialZeroIncrement x h T =
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2) := by
    unfold secondOrderNontrivialZeroIncrement
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hsum]
  exact norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_of_RH
    hRH hx hh hsmall

/-- Uniform `log² T` control of the standardized nontrivial-zero increment. -/
theorem exists_C_norm_secondOrderNontrivialZeroIncrement_le_log_sq :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
        2 * C * x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 := by
  rcases
      exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_log_sq with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x h T hx hh hT hsmall
  have hsum :
      secondOrderNontrivialZeroIncrement x h T =
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2) := by
    unfold secondOrderNontrivialZeroIncrement
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hsum]
  exact hbound x h T hx hh hT hsmall

/-- Uniform `sqrt x log² T` control of the standardized smoothed zero
increment under RH. -/
theorem
    exists_C_norm_secondOrderNontrivialZeroIncrement_le_sqrt_mul_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x h T : ℝ,
      1 ≤ x → 0 ≤ h → 4 ≤ T →
      (T + 1) * Real.log ((x + h) / x) ≤ 1 →
      ‖secondOrderNontrivialZeroIncrement x h T‖ ≤
        2 * C * Real.sqrt x * Real.log ((x + h) / x) *
          (1 + Real.log (T + 6)) ^ 2 := by
  rcases
      exists_C_norm_secondOrderRieszZeroSumWithMultiplicity_increment_le_sqrt_mul_log_sq_of_RH
        hRH with ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro x h T hx hh hT hsmall
  have hsum :
      secondOrderNontrivialZeroIncrement x h T =
        ∑ ρ ∈ nontrivialZerosFinset T,
          -(analyticOrderNatAt riemannZeta ρ : ℂ) *
            ((((x + h : ℝ) : ℂ) ^ ρ - (x : ℂ) ^ ρ) / ρ ^ 2) := by
    unfold secondOrderNontrivialZeroIncrement
    apply Finset.sum_congr rfl
    intro ρ _hρ
    ring
  rw [hsum]
  exact hbound x h T hx hh hT hsmall

/-- Standardized selected-height Riesz sandwich. The abstract residue families
have been eliminated: the endpoint difference is exactly the origin
derivative increment, the main pole contribution `h`, and the canonical
multiplicity-aware nontrivial-zero increment. The remaining error is the
already proved contour-plus-Perron budget. -/
theorem exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          chebyshevPsi x ≤
              ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_crossing_zero_moving_line_neg_one
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with
    ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh
  rcases hbound hx hh with
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, _hzeroX, _hresidueX,
      _hpolesY, _hclassY, _hcompleteY, _hzeroY, _hresidueY,
      hpolesEq, hsumDiff, hbounds⟩
  have hTpos : 0 < T := by linarith [hT.1]
  have hy : 0 < x + h := by
    have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
    linarith
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hy).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) :=
    zero_lt_one.trans_le hlogOne
  let c : ℝ := 1 + 1 / Real.log (x + h)
  have hc : 1 < c := by
    dsimp [c]
    linarith [one_div_pos.mpr hlogpos]
  have honeRect :
      (1 : ℂ) ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ) := by
    rw [Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ c),
      Set.uIcc_of_le (by linarith : -T ≤ T)]
    norm_num
    exact ⟨hc.le, hTpos.le⟩
  have hone : (1 : ℂ) ∈ polesX :=
    hcompleteX 1 (by simpa [c] using honeRect)
      (Or.inr (Or.inl rfl))
  have hsupport :
      (polesX.erase 0).erase 1 = nontrivialZerosFinset T := by
    apply erase_zero_one_poles_eq_nontrivialZerosFinset
      hTpos hc hgood
    · simpa [c] using hpolesX
    · exact hclassX
    · simpa [c] using hcompleteX
  let f : ℂ → ℂ := fun p =>
    -(analyticOrderNatAt riemannZeta p : ℂ) *
      (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2
  have hsum :
      (∑ p ∈ polesX.erase 0,
          if p = 1 then (h : ℂ) else f p) =
        (h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ :=
    sum_erase_zero_ite_one_eq_main_add_nontrivialZeroSum
      f hone hsupport
  subst polesY
  have hstandard :
      (∑ p ∈ polesX, residueY p) -
          (∑ p ∈ polesX, residueX p) =
        secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
          secondOrderNontrivialZeroIncrement x h T := by
    rw [hsum] at hsumDiff
    calc
      (∑ p ∈ polesX, residueY p) -
          (∑ p ∈ polesX, residueX p) =
          (deriv (fun z : ℂ =>
              -logDeriv riemannZeta z *
                ((x + h : ℝ) : ℂ) ^ z) 0 -
            deriv (fun z : ℂ =>
              -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
            ((h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ) := by
        simpa [f] using hsumDiff
      _ = secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
          secondOrderNontrivialZeroIncrement x h T := by
        simp only [secondOrderOriginDerivativeIncrement,
          secondOrderNontrivialZeroIncrement, f]
        ring
  simpa [hstandard] using hbounds

/-- Endpoint-specialized compatibility form of the uniform standardized
selected-height sandwich. -/
theorem exists_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum
    {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          chebyshevPsi x ≤
              ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨T, hT, hgood, hbound hx hh⟩

/-- Selected-height Riesz sandwich with every origin contribution evaluated
explicitly. The only remaining analytic zero term is the canonical finite
multiplicity-aware nontrivial-zero sum. -/
theorem
    exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
          chebyshevPsi x ≤
              ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_standard_zero_sum
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh
  have hbounds := hbound hx hh
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hypos : 0 < x + h := by linarith
  rw [secondOrderOriginDerivativeIncrement_eq hxpos hypos] at hbounds
  exact hbounds

/-- Endpoint-specialized compatibility form of the uniform explicit-origin
selected-height sandwich. -/
theorem
    exists_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum
    {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          chebyshevPsi x ≤
              ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re +
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ∧
            ((-(Real.log (2 * Real.pi) : ℂ) *
                    (Real.log ((x + h) / x) : ℂ) +
                  (h : ℂ) +
                  secondOrderNontrivialZeroIncrement x h T).re -
                secondOrderSelectedHeightTotalBudget C x h A T) /
                  Real.log ((x + h) / x) ≤
              chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨T, hT, hgood, hbound hx hh⟩

/-- Fully scalar selected-height sandwich. A caller-level small-increment
condition at the left endpoint `A` controls the selected `T ∈ [A, A+1]`;
the finite zero sum is then absorbed by its proved `log² T` norm bound. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightTotalBudget C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightTotalBudget C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum
      with ⟨C, hC, hchoose⟩
  rcases exists_C_norm_secondOrderNontrivialZeroIncrement_le_log_sq with
    ⟨D, hD, hzero⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmallA
  have hbounds := hbound hx hh
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := by
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hsmallT :
      (T + 1) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 1) * Real.log ((x + h) / x) ≤
          (A + 2) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  let Z := secondOrderNontrivialZeroIncrement x h T
  let B :=
    2 * D * x * Real.log ((x + h) / x) *
      (1 + Real.log (T + 6)) ^ 2
  have hnorm : ‖Z‖ ≤ B := by
    simpa only [Z, B] using
      hzero x h T hxone hh.le (hA.trans hT.1) hsmallT
  have habs : |Z.re| ≤ B :=
    (Complex.abs_re_le_norm Z).trans hnorm
  have hre : -B ≤ Z.re ∧ Z.re ≤ B := abs_le.mp habs
  have hreal :
      (-(Real.log (2 * Real.pi) : ℂ) *
              (Real.log ((x + h) / x) : ℂ) +
            (h : ℂ) + Z).re =
        h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) + Z.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  change
    chebyshevPsi x ≤
          ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re +
              secondOrderSelectedHeightTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
      ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re -
              secondOrderSelectedHeightTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) at hbounds
  rw [hreal] at hbounds
  refine ⟨?_, ?_⟩
  · exact hbounds.1.trans
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.2]))
  · exact
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.1])).trans hbounds.2

/-- Under RH, the uniform scalar selected-height sandwich retains the
square-root scale of the smoothed zero increment. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightTotalBudget C x h A T +
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightTotalBudget C x h A T -
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum
      with ⟨C, hC, hchoose⟩
  rcases
      exists_C_norm_secondOrderNontrivialZeroIncrement_le_sqrt_mul_log_sq_of_RH
        hRH with ⟨D, hD, hzero⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmallA
  have hbounds := hbound hx hh
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hxone : 1 ≤ x := by
    exact (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hsmallT :
      (T + 1) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 1) * Real.log ((x + h) / x) ≤
          (A + 2) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  let Z := secondOrderNontrivialZeroIncrement x h T
  let B :=
    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
      (1 + Real.log (T + 6)) ^ 2
  have hnorm : ‖Z‖ ≤ B := by
    simpa only [Z, B] using
      hzero x h T hxone hh.le (hA.trans hT.1) hsmallT
  have habs : |Z.re| ≤ B :=
    (Complex.abs_re_le_norm Z).trans hnorm
  have hre : -B ≤ Z.re ∧ Z.re ≤ B := abs_le.mp habs
  have hreal :
      (-(Real.log (2 * Real.pi) : ℂ) *
              (Real.log ((x + h) / x) : ℂ) +
            (h : ℂ) + Z).re =
        h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) + Z.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  change
    chebyshevPsi x ≤
          ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re +
              secondOrderSelectedHeightTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
      ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re -
              secondOrderSelectedHeightTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) at hbounds
  rw [hreal] at hbounds
  refine ⟨?_, ?_⟩
  · exact hbounds.1.trans
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.2]))
  · exact
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.1])).trans hbounds.2

/-- Endpoint-specialized compatibility form of the uniform scalar
selected-height sandwich. -/
theorem
    exists_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq
    {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      (A + 2) * Real.log ((x + h) / x) ≤ 1 →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightTotalBudget C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightTotalBudget C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq
      with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA hsmall
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨T, hT, hgood, hbound hx hh hsmall⟩

/-- The logarithmic Riesz difference quotient has the same scale as its
left endpoint.  This elementary two-sided estimate is what converts the
selected-height sandwich into an error bound centered at `x`. -/
theorem smoothingIncrementDivLog_mem_Icc
    {x h : ℝ} (hx : 0 < x) (hh : 0 < h) :
    h / Real.log ((x + h) / x) ∈ Set.Icc x (x + h) := by
  have hy : 0 < x + h := by linarith
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hx]
    linarith
  have hratioPos : 0 < (x + h) / x := zero_lt_one.trans hratio
  have hlogPos : 0 < Real.log ((x + h) / x) := Real.log_pos hratio
  have hlogUpper :
      Real.log ((x + h) / x) ≤ h / x := by
    have hlog :=
      Real.log_le_sub_one_of_pos hratioPos
    calc
      Real.log ((x + h) / x) ≤ (x + h) / x - 1 := hlog
      _ = h / x := by field_simp; ring
  have hlogLower :
      h / (x + h) ≤ Real.log ((x + h) / x) := by
    have hlog :=
      Real.one_sub_inv_le_log_of_pos hratioPos
    calc
      h / (x + h) = 1 - ((x + h) / x)⁻¹ := by
        field_simp
        ring
      _ ≤ Real.log ((x + h) / x) := hlog
  constructor
  · apply (le_div_iff₀ hlogPos).2
    calc
      x * Real.log ((x + h) / x) ≤ x * (h / x) :=
        mul_le_mul_of_nonneg_left hlogUpper hx.le
      _ = h := by field_simp
  · apply (div_le_iff₀ hlogPos).2
    calc
      h = (x + h) * (h / (x + h)) := by field_simp
      _ ≤ (x + h) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_left hlogLower hy.le

/-- The fully scalar selected-height sandwich rewritten as endpoint errors
centered at `x`.  The Riesz main quotient contributes at most the smoothing
width `h`; the zero package contributes the explicit `log² T` term, and the
contour-plus-Perron error remains as its exact selected-height budget divided
by the logarithmic increment. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq with
    ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hbounds := hbound hx hh hsmall
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hquotient :=
    smoothingIncrementDivLog_mem_Icc hxpos hh
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  refine ⟨?_, ?_⟩
  · calc
      chebyshevPsi x - x ≤
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                secondOrderSelectedHeightTotalBudget C x h A T +
                2 * D * x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) - x :=
        sub_le_sub_right hbounds.1 x
      _ =
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) +
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 - x := by
        field_simp [hlogpos.ne']
      _ ≤
          h - Real.log (2 * Real.pi) +
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.2]
  · calc
      x - Real.log (2 * Real.pi) -
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) -
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.1]
      _ =
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                secondOrderSelectedHeightTotalBudget C x h A T -
                2 * D * x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) := by
        field_simp [hlogpos.ne']
      _ ≤ chebyshevPsi (x + h) := hbounds.2

/-- Under RH, the centered endpoint error keeps the square-root zero-sum
term after division by the logarithmic smoothing increment. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_sqrt_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_of_RH
        hRH with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hbounds := hbound hx hh hsmall
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hquotient :=
    smoothingIncrementDivLog_mem_Icc hxpos hh
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  refine ⟨?_, ?_⟩
  · calc
      chebyshevPsi x - x ≤
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                secondOrderSelectedHeightTotalBudget C x h A T +
                2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) - x :=
        sub_le_sub_right hbounds.1 x
      _ =
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) +
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 - x := by
        field_simp [hlogpos.ne']
      _ ≤
          h - Real.log (2 * Real.pi) +
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.2]
  · calc
      x - Real.log (2 * Real.pi) -
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) -
              secondOrderSelectedHeightTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.1]
      _ =
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                secondOrderSelectedHeightTotalBudget C x h A T -
                2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) := by
        field_simp [hlogpos.ne']
      _ ≤ chebyshevPsi (x + h) := hbounds.2

/-- Endpoint-specialized compatibility form of the uniform centered endpoint
error estimate. -/
theorem
    exists_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq
    {x h : ℝ} (hx : Real.exp 1 ≤ x) (hh : 0 < h) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      (A + 2) * Real.log ((x + h) / x) ≤ 1 →
        ∃ T ∈ Set.Icc A (A + 1),
          ExplicitFormulaAux.goodHeight T ∧
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq
      with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA hsmall
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨T, hT, hgood, hbound hx hh hsmall⟩

/-- A canonical smoothing width whose logarithmic increment is automatically
small enough for every selected height in `[A, A+1]`.  It saturates the
caller-level constraint exactly. -/
noncomputable def canonicalSecondOrderSmoothingWidth
    (x A : ℝ) : ℝ :=
  x * (Real.exp (1 / (A + 2)) - 1)

theorem canonicalSecondOrderSmoothingWidth_pos
    {x A : ℝ} (hx : 0 < x) (hA : 4 ≤ A) :
    0 < canonicalSecondOrderSmoothingWidth x A := by
  unfold canonicalSecondOrderSmoothingWidth
  have hq : 0 < A + 2 := by linarith
  have hexp : 1 < Real.exp (1 / (A + 2)) :=
    Real.one_lt_exp_iff.mpr (one_div_pos.mpr hq)
  exact mul_pos hx (sub_pos.mpr hexp)

theorem canonicalSecondOrderSmoothingWidth_log_eq
    {x A : ℝ} (hx : 0 < x) :
    Real.log
        ((x + canonicalSecondOrderSmoothingWidth x A) / x) =
      1 / (A + 2) := by
  have hxne : x ≠ 0 := hx.ne'
  have hratio :
      (x + canonicalSecondOrderSmoothingWidth x A) / x =
        Real.exp (1 / (A + 2)) := by
    unfold canonicalSecondOrderSmoothingWidth
    field_simp
    ring
  rw [hratio, Real.log_exp]

theorem canonicalSecondOrderSmoothingWidth_small
    {x A : ℝ} (hx : 0 < x) (hA : 4 ≤ A) :
    (A + 2) *
        Real.log
          ((x + canonicalSecondOrderSmoothingWidth x A) / x) ≤ 1 := by
  have hq : 0 < A + 2 := by linarith
  rw [canonicalSecondOrderSmoothingWidth_log_eq hx]
  field_simp
  norm_num

/-- The canonical width is not merely admissible: among nonnegative widths it
is the largest one satisfying the selected-height small-increment constraint.
Thus the specialization does not lose smoothing range before the analytic
budget is optimized. -/
theorem le_canonicalSecondOrderSmoothingWidth_of_small
    {x h A : ℝ} (hx : 0 < x) (hh : 0 ≤ h) (hA : 4 ≤ A)
    (hsmall :
      (A + 2) * Real.log ((x + h) / x) ≤ 1) :
    h ≤ canonicalSecondOrderSmoothingWidth x A := by
  have hq : 0 < A + 2 := by linarith
  have hy : 0 < x + h := by linarith
  have hratioPos : 0 < (x + h) / x := div_pos hy hx
  have hlog :
      Real.log ((x + h) / x) ≤ 1 / (A + 2) := by
    apply (le_div_iff₀ hq).2
    simpa [mul_comm] using hsmall
  have hratio :
      (x + h) / x ≤ Real.exp (1 / (A + 2)) := by
    calc
      (x + h) / x =
          Real.exp (Real.log ((x + h) / x)) := by
        rw [Real.exp_log hratioPos]
      _ ≤ Real.exp (1 / (A + 2)) := Real.exp_le_exp.mpr hlog
  have hmul :
      x + h ≤ Real.exp (1 / (A + 2)) * x :=
    (div_le_iff₀ hx).mp hratio
  unfold canonicalSecondOrderSmoothingWidth
  nlinarith [hmul]

/-- Canonical selected-height endpoint estimate.  The free smoothing width is
specialized to the maximal admissible value, so no small-increment premise
remains for the caller.  The contour and zero-mass constants are absolute and
precede both the height interval and endpoint.  This is still an admissible
specialization, not a total-budget optimization theorem: the maximal
admissible width need not minimize the displayed budget. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_canonical_smoothing_error :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x : ℝ}, Real.exp 1 ≤ x →
          chebyshevPsi x - x ≤
              canonicalSecondOrderSmoothingWidth x A -
                Real.log (2 * Real.pi) +
                secondOrderSelectedHeightTotalBudget C x
                    (canonicalSecondOrderSmoothingWidth x A) A T /
                  Real.log
                    ((x + canonicalSecondOrderSmoothingWidth x A) / x) +
                2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  secondOrderSelectedHeightTotalBudget C x
                      (canonicalSecondOrderSmoothingWidth x A) A T /
                    Real.log
                      ((x + canonicalSecondOrderSmoothingWidth x A) / x) -
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
              chebyshevPsi
                (x + canonicalSecondOrderSmoothingWidth x A) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq
      with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hh :
      0 < canonicalSecondOrderSmoothingWidth x A :=
    canonicalSecondOrderSmoothingWidth_pos hxpos hA
  exact hbound hx hh (canonicalSecondOrderSmoothingWidth_small hxpos hA)

/-- Under RH, the canonical smoothing specialization has an absolute
selected-height contour constant and a `sqrt x log² T` zero contribution. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_canonical_smoothing_error_sqrt_log_sq_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x : ℝ}, Real.exp 1 ≤ x →
          chebyshevPsi x - x ≤
              canonicalSecondOrderSmoothingWidth x A -
                Real.log (2 * Real.pi) +
                secondOrderSelectedHeightTotalBudget C x
                    (canonicalSecondOrderSmoothingWidth x A) A T /
                  Real.log
                    ((x + canonicalSecondOrderSmoothingWidth x A) / x) +
                2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  secondOrderSelectedHeightTotalBudget C x
                      (canonicalSecondOrderSmoothingWidth x A) A T /
                    Real.log
                      ((x + canonicalSecondOrderSmoothingWidth x A) / x) -
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
              chebyshevPsi
                (x + canonicalSecondOrderSmoothingWidth x A) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_sqrt_log_sq_of_RH
        hRH with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x hx
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hh :
      0 < canonicalSecondOrderSmoothingWidth x A :=
    canonicalSecondOrderSmoothingWidth_pos hxpos hA
  exact hbound hx hh (canonicalSecondOrderSmoothingWidth_small hxpos hA)

/-- Fixed-`x,A` compatibility form of the uniform canonical smoothing
estimate. -/
theorem
    exists_C_D_goodHeight_chebyshevPsi_canonical_smoothing_error
    {x A : ℝ} (hx : Real.exp 1 ≤ x) (hA : 4 ≤ A) :
    ∃ C D T : ℝ,
      0 ≤ C ∧ 0 ≤ D ∧ T ∈ Set.Icc A (A + 1) ∧
        ExplicitFormulaAux.goodHeight T ∧
          chebyshevPsi x - x ≤
              canonicalSecondOrderSmoothingWidth x A -
                Real.log (2 * Real.pi) +
                secondOrderSelectedHeightTotalBudget C x
                    (canonicalSecondOrderSmoothingWidth x A) A T /
                  Real.log
                    ((x + canonicalSecondOrderSmoothingWidth x A) / x) +
                2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
            x - Real.log (2 * Real.pi) -
                  secondOrderSelectedHeightTotalBudget C x
                      (canonicalSecondOrderSmoothingWidth x A) A T /
                    Real.log
                      ((x + canonicalSecondOrderSmoothingWidth x A) / x) -
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
              chebyshevPsi
                (x + canonicalSecondOrderSmoothingWidth x A) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_canonical_smoothing_error
      with ⟨C, D, hC, hD, hchoose⟩
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  exact ⟨C, D, T, hC, hD, hT, hgood, hbound hx⟩

/-- The cancellation-aware contour estimate feeds the actual moving-line
second-order formula and Riesz sandwich.  The residue family is eliminated in
favor of the explicit origin term, the main-pole increment, and the canonical
multiplicity-aware finite zero sum. -/
theorem
    exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum_increment :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (T + 2) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                ((-(Real.log (2 * Real.pi) : ℂ) *
                      (Real.log ((x + h) / x) : ℂ) +
                    (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ∧
              ((-(Real.log (2 * Real.pi) : ℂ) *
                      (Real.log ((x + h) / x) : ℂ) +
                    (h : ℂ) +
                    secondOrderNontrivialZeroIncrement x h T).re -
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
                    Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_goodHeight_Icc_norm_secondOrderContourRemainder_increment_le
      with ⟨C, hC, hchoose⟩
  refine ⟨C, hC, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hremainderAll⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hexpOne : 1 < Real.exp 1 := Real.one_lt_exp_iff.mpr zero_lt_one
  have hx1 : 1 < x := hexpOne.trans_le hx
  have hy1 : 1 < x + h := by linarith
  have hypos : 0 < x + h := zero_lt_one.trans hy1
  have hlogOne : 1 ≤ Real.log (x + h) :=
    (Real.le_log_iff_exp_le hypos).2 (hx.trans (by linarith))
  have hlogpos : 0 < Real.log (x + h) := zero_lt_one.trans_le hlogOne
  let c : ℝ := 1 + 1 / Real.log (x + h)
  have hc : 1 < c := by
    dsimp [c]
    linarith [one_div_pos.mpr hlogpos]
  rcases hremainderAll hx hh hsmall with ⟨hboundary, hremainder⟩
  have hTpos : 0 < T := by linarith [hT.1]
  let W : ℝ := T / (2 * Real.pi)
  have hW : 0 < W := by
    dsimp [W]
    positivity
  have hscale : 2 * Real.pi * W = T := by
    dsimp [W]
    field_simp [Real.pi_ne_zero]
  have hboundaryW :
      ∀ p ∈
        ([[(-1 : ℝ), c]] ×ℂ
          [[-(2 * Real.pi * W), 2 * Real.pi * W]] : Set ℂ),
        p = 0 ∨ p = 1 ∨ riemannZeta p = 0 →
          -1 < p.re ∧ p.re < c ∧
            -(2 * Real.pi * W) < p.im ∧
              p.im < 2 * Real.pi * W := by
    simpa [c, hscale] using hboundary
  rcases
      exists_chebyshevPsi_bounds_of_secondOrderExplicitFormula_crossing_zero_moving_line
        (a := -1) (W := W) hx1 hh (by norm_num) hW
          (by simpa [c] using hboundaryW) with
    ⟨polesX, residueX, polesY, residueY,
      hpolesX, hclassX, hcompleteX, hzeroX, hresidueX,
      hpolesY, hclassY, hcompleteY, hzeroY, hresidueY, hbounds⟩
  let RX : ℂ := secondOrderContourRemainder x (-1) c W
  let RY : ℂ := secondOrderContourRemainder (x + h) (-1) c W
  let SX : ℂ := ∑ p ∈ polesX, residueX p
  let SY : ℂ := ∑ p ∈ polesY, residueY p
  let BC : ℝ :=
    secondOrderSelectedHeightIncrementContourBudget C x h A T
  let BP : ℝ := secondOrderMovingEndpointPerronBudget x h W
  have hremainder' : ‖RY - RX‖ ≤ BC := by
    simpa [RX, RY, BC, W, c, hscale] using hremainder
  have hremainderRe : |(RY - RX).re| ≤ BC :=
    (abs_re_le_norm (RY - RX)).trans hremainder'
  rcases abs_le.mp hremainderRe with
    ⟨hremainderLower, hremainderUpper⟩
  have hbounds' :
      chebyshevPsi x ≤
          (((SY - RY) - (SX - RX)).re + BP) /
            Real.log ((x + h) / x) ∧
        (((SY - RY) - (SX - RX)).re - BP) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) := by
    simpa [SX, SY, RX, RY, BP, c, W] using hbounds
  have hdecomp :
      ((SY - RY) - (SX - RX)).re =
        (SY - SX).re - (RY - RX).re := by
    simp
    ring
  have htotal :
      secondOrderSelectedHeightIncrementTotalBudget C x h A T = BC + BP := by
    rfl
  have hratio : 1 < (x + h) / x :=
    (lt_div_iff₀ (zero_lt_one.trans hx1)).2 (by linarith)
  have hlogratio : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hpolesEq : polesX = polesY := by
    ext p
    constructor
    · intro hp
      have hpBounds := hpolesX p hp
      apply hcompleteY p
      · rw [Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
            1 + 1 / Real.log (x + h)),
          Set.uIcc_of_le (by linarith [hW] :
            -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
        exact
          ⟨⟨hpBounds.1.le, hpBounds.2.1.le⟩,
            ⟨hpBounds.2.2.1.le, hpBounds.2.2.2.le⟩⟩
      · exact hclassX p hp
    · intro hp
      have hpBounds := hpolesY p hp
      apply hcompleteX p
      · rw [Complex.mem_reProdIm,
          Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
            1 + 1 / Real.log (x + h)),
          Set.uIcc_of_le (by linarith [hW] :
            -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
        exact
          ⟨⟨hpBounds.1.le, hpBounds.2.1.le⟩,
            ⟨hpBounds.2.2.1.le, hpBounds.2.2.2.le⟩⟩
      · exact hclassY p hp
  subst polesY
  have hzeroMem : 0 ∈ polesX := by
    apply hcompleteX 0
    · rw [Complex.mem_reProdIm,
        Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤
          1 + 1 / Real.log (x + h)),
        Set.uIcc_of_le (by linarith [hW] :
          -(2 * Real.pi * W) ≤ 2 * Real.pi * W)]
      simp only [Complex.zero_re, Complex.zero_im, Set.mem_Icc]
      constructor
      · constructor <;> linarith
      · constructor <;> nlinarith [Real.pi_pos]
    · exact Or.inl rfl
  have hsumDiff :
      (∑ p ∈ polesX, residueY p) -
          (∑ p ∈ polesX, residueX p) =
        (deriv (fun z : ℂ =>
            -logDeriv riemannZeta z *
              ((x + h : ℝ) : ℂ) ^ z) 0 -
          deriv (fun z : ℂ =>
            -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
          ∑ p ∈ polesX.erase 0,
            if p = 1 then (h : ℂ)
            else -(analyticOrderNatAt riemannZeta p : ℂ) *
              (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2 := by
    rw [show (∑ p ∈ polesX, residueY p) =
        (∑ p ∈ polesX.erase 0, residueY p) + residueY 0 by
          exact (Finset.sum_erase_add _ _ hzeroMem).symm]
    rw [show (∑ p ∈ polesX, residueX p) =
        (∑ p ∈ polesX.erase 0, residueX p) + residueX 0 by
          exact (Finset.sum_erase_add _ _ hzeroMem).symm]
    rw [hzeroY, hzeroX]
    rw [show
        (∑ p ∈ polesX.erase 0, residueY p) +
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 -
            ((∑ p ∈ polesX.erase 0, residueX p) +
              deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) =
          (deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * ((x + h : ℝ) : ℂ) ^ z) 0 -
            deriv (fun z : ℂ =>
                -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
            ((∑ p ∈ polesX.erase 0, residueY p) -
              (∑ p ∈ polesX.erase 0, residueX p)) by ring]
    rw [← Finset.sum_sub_distrib]
    congr 1
    apply Finset.sum_congr rfl
    intro p hp
    have hpMem : p ∈ polesX := Finset.mem_of_mem_erase hp
    have hp0 : p ≠ 0 := Finset.ne_of_mem_erase hp
    rw [hresidueY p hpMem hp0, hresidueX p hpMem hp0]
    split_ifs with hp1
    · subst p
      norm_num
    · ring
  have hresidueBounds :
      chebyshevPsi x ≤
          ((SY - SX).re +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
        ((SY - SX).re -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) := by
    constructor
    · calc
        chebyshevPsi x ≤
            (((SY - RY) - (SX - RX)).re + BP) /
              Real.log ((x + h) / x) := hbounds'.1
        _ ≤ ((SY - SX).re +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) := by
          apply (div_le_div_iff_of_pos_right hlogratio).2
          rw [hdecomp, htotal]
          linarith
    · calc
        ((SY - SX).re -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤
            (((SY - RY) - (SX - RX)).re - BP) /
              Real.log ((x + h) / x) := by
          apply (div_le_div_iff_of_pos_right hlogratio).2
          rw [hdecomp, htotal]
          linarith
        _ ≤ chebyshevPsi (x + h) := hbounds'.2
  have honeRect :
      (1 : ℂ) ∈
        ([[(-1 : ℝ), c]] ×ℂ [[-T, T]] : Set ℂ) := by
    rw [Complex.mem_reProdIm,
      Set.uIcc_of_le (by linarith : (-1 : ℝ) ≤ c),
      Set.uIcc_of_le (by linarith : -T ≤ T)]
    norm_num
    exact ⟨hc.le, hTpos.le⟩
  have hone : (1 : ℂ) ∈ polesX :=
    hcompleteX 1 (by simpa [c, hscale] using honeRect)
      (Or.inr (Or.inl rfl))
  have hsupport :
      (polesX.erase 0).erase 1 = nontrivialZerosFinset T := by
    apply erase_zero_one_poles_eq_nontrivialZerosFinset
      hTpos hc hgood
    · simpa [c, hscale] using hpolesX
    · exact hclassX
    · simpa [c, hscale] using hcompleteX
  let f : ℂ → ℂ := fun p =>
    -(analyticOrderNatAt riemannZeta p : ℂ) *
      (((x + h : ℝ) : ℂ) ^ p - (x : ℂ) ^ p) / p ^ 2
  have hsum :
      (∑ p ∈ polesX.erase 0,
          if p = 1 then (h : ℂ) else f p) =
        (h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ :=
    sum_erase_zero_ite_one_eq_main_add_nontrivialZeroSum
      f hone hsupport
  have hstandard :
      SY - SX =
        secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
          secondOrderNontrivialZeroIncrement x h T := by
    rw [hsum] at hsumDiff
    calc
      SY - SX =
          (deriv (fun z : ℂ =>
              -logDeriv riemannZeta z *
                ((x + h : ℝ) : ℂ) ^ z) 0 -
            deriv (fun z : ℂ =>
              -logDeriv riemannZeta z * (x : ℂ) ^ z) 0) +
            ((h : ℂ) + ∑ ρ ∈ nontrivialZerosFinset T, f ρ) := by
        simpa [SX, SY, f] using hsumDiff
      _ = secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
          secondOrderNontrivialZeroIncrement x h T := by
        simp only [secondOrderOriginDerivativeIncrement,
          secondOrderNontrivialZeroIncrement, f]
        ring
  have hstandardBounds :
      chebyshevPsi x ≤
          ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                secondOrderNontrivialZeroIncrement x h T).re +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
        ((secondOrderOriginDerivativeIncrement x h + (h : ℂ) +
                secondOrderNontrivialZeroIncrement x h T).re -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) := by
    simpa [hstandard] using hresidueBounds
  rw [secondOrderOriginDerivativeIncrement_eq
    (zero_lt_one.trans hx1) hypos] at hstandardBounds
  exact hstandardBounds

/-- Scalar cancellation-aware selected-height sandwich.  The caller-level
`A+3` condition controls the `T+2` horizontal cancellation hypothesis at the
selected height and also the `T+1` finite-zero-sum estimate. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq_increment :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                    2 * D * x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum_increment
      with ⟨C, hC, hchoose⟩
  rcases exists_C_norm_secondOrderNontrivialZeroIncrement_le_log_sq with
    ⟨D, hD, hzero⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmallA
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hsmallContour :
      (T + 2) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 2) * Real.log ((x + h) / x) ≤
          (A + 3) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  have hbounds := hbound hx hh hsmallContour
  have hxone : 1 ≤ x :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hsmallZero :
      (T + 1) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 1) * Real.log ((x + h) / x) ≤
          (A + 3) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  let Z := secondOrderNontrivialZeroIncrement x h T
  let B :=
    2 * D * x * Real.log ((x + h) / x) *
      (1 + Real.log (T + 6)) ^ 2
  have hnorm : ‖Z‖ ≤ B := by
    simpa only [Z, B] using
      hzero x h T hxone hh.le (hA.trans hT.1) hsmallZero
  have habs : |Z.re| ≤ B :=
    (Complex.abs_re_le_norm Z).trans hnorm
  have hre : -B ≤ Z.re ∧ Z.re ≤ B := abs_le.mp habs
  have hreal :
      (-(Real.log (2 * Real.pi) : ℂ) *
              (Real.log ((x + h) / x) : ℂ) +
            (h : ℂ) + Z).re =
        h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) + Z.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  change
    chebyshevPsi x ≤
          ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
      ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) at hbounds
  rw [hreal] at hbounds
  refine ⟨?_, ?_⟩
  · exact hbounds.1.trans
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.2]))
  · exact
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.1])).trans hbounds.2

/-- The scalar cancellation-aware sandwich rewritten as endpoint errors
centered at `x`.  This is the callable `chebyshevPsi` endpoint form of the
subtracted-kernel contour estimate. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_log_sq_increment :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_log_sq_increment
      with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hbounds := hbound hx hh hsmall
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hquotient := smoothingIncrementDivLog_mem_Icc hxpos hh
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  refine ⟨?_, ?_⟩
  · calc
      chebyshevPsi x - x ≤
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                2 * D * x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) - x :=
        sub_le_sub_right hbounds.1 x
      _ =
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 - x := by
        field_simp [hlogpos.ne']
      _ ≤
          h - Real.log (2 * Real.pi) +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.2]
  · calc
      x - Real.log (2 * Real.pi) -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 ≤
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.1]
      _ =
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                2 * D * x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) := by
        field_simp [hlogpos.ne']
      _ ≤ chebyshevPsi (x + h) := hbounds.2

/-- Under RH, the cancellation-aware scalar sandwich retains the
`sqrt x log² T` scale of the finite zero increment. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_increment_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x ≤
                (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ∧
              (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                      (1 + Real.log (T + 6)) ^ 2) /
                  Real.log ((x + h) / x) ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_forall_goodHeight_chebyshevPsi_bounds_explicit_origin_zero_sum_increment
      with ⟨C, hC, hchoose⟩
  rcases
      exists_C_norm_secondOrderNontrivialZeroIncrement_le_sqrt_mul_log_sq_of_RH
        hRH with ⟨D, hD, hzero⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmallA
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hsmallContour :
      (T + 2) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 2) * Real.log ((x + h) / x) ≤
          (A + 3) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  have hbounds := hbound hx hh hsmallContour
  have hxone : 1 ≤ x :=
    (Real.one_lt_exp_iff.mpr zero_lt_one).le.trans hx
  have hsmallZero :
      (T + 1) * Real.log ((x + h) / x) ≤ 1 := by
    calc
      (T + 1) * Real.log ((x + h) / x) ≤
          (A + 3) * Real.log ((x + h) / x) :=
        mul_le_mul_of_nonneg_right (by linarith [hT.2]) hlogpos.le
      _ ≤ 1 := hsmallA
  let Z := secondOrderNontrivialZeroIncrement x h T
  let B :=
    2 * D * Real.sqrt x * Real.log ((x + h) / x) *
      (1 + Real.log (T + 6)) ^ 2
  have hnorm : ‖Z‖ ≤ B := by
    simpa only [Z, B] using
      hzero x h T hxone hh.le (hA.trans hT.1) hsmallZero
  have habs : |Z.re| ≤ B :=
    (Complex.abs_re_le_norm Z).trans hnorm
  have hre : -B ≤ Z.re ∧ Z.re ≤ B := abs_le.mp habs
  have hreal :
      (-(Real.log (2 * Real.pi) : ℂ) *
              (Real.log ((x + h) / x) : ℂ) +
            (h : ℂ) + Z).re =
        h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) + Z.re := by
    simp only [Complex.add_re, Complex.mul_re, Complex.neg_re,
      Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
    ring
  change
    chebyshevPsi x ≤
          ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ∧
      ((-(Real.log (2 * Real.pi) : ℂ) *
                  (Real.log ((x + h) / x) : ℂ) +
                (h : ℂ) + Z).re -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T) /
            Real.log ((x + h) / x) ≤ chebyshevPsi (x + h) at hbounds
  rw [hreal] at hbounds
  refine ⟨?_, ?_⟩
  · exact hbounds.1.trans
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.2]))
  · exact
      ((div_le_div_iff_of_pos_right hlogpos).2 (by
        dsimp only [B] at hre ⊢
        linarith [hre.1])).trans hbounds.2

/-- RH-specialized cancellation-aware endpoint errors centered at `x`. -/
theorem
    exists_uniform_C_D_forall_goodHeight_chebyshevPsi_endpoint_error_sqrt_log_sq_increment_of_RH
    (hRH : RiemannHypothesis.Statement) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ A : ℝ, 4 ≤ A →
      ∃ T ∈ Set.Icc A (A + 1),
        ExplicitFormulaAux.goodHeight T ∧
          ∀ {x h : ℝ}, Real.exp 1 ≤ x → 0 < h →
            (A + 3) * Real.log ((x + h) / x) ≤ 1 →
            chebyshevPsi x - x ≤
                h - Real.log (2 * Real.pi) +
                  secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                    Real.log ((x + h) / x) +
                  2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ∧
              x - Real.log (2 * Real.pi) -
                    secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                      Real.log ((x + h) / x) -
                    2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
                chebyshevPsi (x + h) := by
  rcases
      exists_uniform_C_D_forall_goodHeight_chebyshevPsi_bounds_scalar_sqrt_log_sq_increment_of_RH
        hRH with ⟨C, D, hC, hD, hchoose⟩
  refine ⟨C, D, hC, hD, ?_⟩
  intro A hA
  rcases hchoose A hA with ⟨T, hT, hgood, hbound⟩
  refine ⟨T, hT, hgood, ?_⟩
  intro x h hx hh hsmall
  have hbounds := hbound hx hh hsmall
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hquotient := smoothingIncrementDivLog_mem_Icc hxpos hh
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  refine ⟨?_, ?_⟩
  · calc
      chebyshevPsi x - x ≤
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) +
                secondOrderSelectedHeightIncrementTotalBudget C x h A T +
                2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) - x :=
        sub_le_sub_right hbounds.1 x
      _ =
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 - x := by
        field_simp [hlogpos.ne']
      _ ≤
          h - Real.log (2 * Real.pi) +
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) +
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.2]
  · calc
      x - Real.log (2 * Real.pi) -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 ≤
          h / Real.log ((x + h) / x) -
              Real.log (2 * Real.pi) -
              secondOrderSelectedHeightIncrementTotalBudget C x h A T /
                Real.log ((x + h) / x) -
              2 * D * Real.sqrt x * (1 + Real.log (T + 6)) ^ 2 := by
        linarith [hquotient.1]
      _ =
          (h - Real.log (2 * Real.pi) * Real.log ((x + h) / x) -
                secondOrderSelectedHeightIncrementTotalBudget C x h A T -
                2 * D * Real.sqrt x * Real.log ((x + h) / x) *
                  (1 + Real.log (T + 6)) ^ 2) /
              Real.log ((x + h) / x) := by
        field_simp [hlogpos.ne']
      _ ≤ chebyshevPsi (x + h) := hbounds.2

/-- At fixed admissible parameters, the cancellation-aware centered upper
endpoint bound is strictly smaller, and the lower endpoint bound is strictly
larger, than the corresponding separate-endpoint expressions. -/
theorem secondOrderSelectedHeightIncrement_endpoint_bounds_strictly_improve
    {C D x h A T : ℝ}
    (hC : 0 < C) (hx : Real.exp 1 ≤ x) (hh : 0 < h)
    (hA : 4 ≤ A) (hT : T ∈ Set.Icc A (A + 1))
    (hsmall : (T + 2) * Real.log ((x + h) / x) ≤ 1) :
    h - Real.log (2 * Real.pi) +
          secondOrderSelectedHeightIncrementTotalBudget C x h A T /
            Real.log ((x + h) / x) +
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 <
        h - Real.log (2 * Real.pi) +
          secondOrderSelectedHeightTotalBudget C x h A T /
            Real.log ((x + h) / x) +
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 ∧
      x - Real.log (2 * Real.pi) -
          secondOrderSelectedHeightTotalBudget C x h A T /
            Real.log ((x + h) / x) -
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 <
        x - Real.log (2 * Real.pi) -
          secondOrderSelectedHeightIncrementTotalBudget C x h A T /
            Real.log ((x + h) / x) -
          2 * D * x * (1 + Real.log (T + 6)) ^ 2 := by
  have hxpos : 0 < x := (Real.exp_pos 1).trans_le hx
  have hratio : 1 < (x + h) / x := by
    rw [lt_div_iff₀ hxpos]
    linarith
  have hlogpos : 0 < Real.log ((x + h) / x) :=
    Real.log_pos hratio
  have hbudget :=
    secondOrderSelectedHeightIncrementTotalBudget_lt
      hC hx hh hA hT hsmall
  constructor
  · have hdiv := div_lt_div_of_pos_right hbudget hlogpos
    linarith
  · have hdiv := div_lt_div_of_pos_right hbudget hlogpos
    linarith

end ExplicitFormulaResidues

end PrimeNumberTheorem
