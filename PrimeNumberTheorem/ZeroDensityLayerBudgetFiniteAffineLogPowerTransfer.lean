import PrimeNumberTheorem.ZeroDensityLayerBudgetFiniteAffinePowerTransfer
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonLogAbsorption

/-!
# Finite affine power transfer with a fourth logarithmic factor

Carlson's proved density estimate carries a fourth power of the logarithm.
The pure affine power transfer therefore needs one additional analytic step.
This module treats one contour term without a logarithm and finitely many
density-strip terms with `(log x)^4`.

A common affine margin `delta` bounds the whole expression by

`totalCoeff * x ^ (-delta) * (1 + (log x)^4)`.

When `delta > 0`, the pure negative power tends to zero and its product with
the fourth logarithmic power also tends to zero.  Thus the same optimized
affine certificate absorbs Carlson's logarithmic loss without changing the
chosen balanced height exponent.
-/

noncomputable section

namespace PrimeNumberTheorem

open Filter

/-- One contour power term together with finitely many affine density terms,
each carrying Carlson's fourth logarithmic power. -/
def finiteAffineDensityLogPowerMajorant
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (floor alpha : ℝ)
    (ceiling slope : Fin (n + 1) → ℝ)
    (x : ℝ) : ℝ :=
  contourCoeff * x ^ (floor - alpha) +
    ∑ i,
      stripCoeff i * x ^ (slope i * alpha - ceiling i) *
        (Real.log x) ^ (4 : ℕ)

/-- The common power-log envelope produced after applying one affine margin
certificate to every contribution. -/
def finiteAffineDensityCommonLogPower
    {n : ℕ} (contourCoeff : ℝ)
    (stripCoeff : Fin (n + 1) → ℝ)
    (delta x : ℝ) : ℝ :=
  finiteAffineDensityTotalCoeff contourCoeff stripCoeff *
    x ^ (-delta) * (1 + (Real.log x) ^ (4 : ℕ))

/-- Nonnegative coefficients make the finite affine power-log majorant
nonnegative on the nonnegative real axis. -/
theorem finiteAffineDensityLogPowerMajorant_nonneg
    {n : ℕ} {contourCoeff floor alpha x : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hx : 0 ≤ x) :
    0 ≤
      finiteAffineDensityLogPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope x := by
  unfold finiteAffineDensityLogPowerMajorant
  apply add_nonneg
  · exact mul_nonneg hcontourCoeff (Real.rpow_nonneg hx _)
  · apply Finset.sum_nonneg
    intro i _hi
    exact mul_nonneg
      (mul_nonneg (hstripCoeff i) (Real.rpow_nonneg hx _))
      (by positivity)

/-- A common affine margin compresses the contour and every logarithmically
weighted density strip to one common power-log envelope. -/
theorem finiteAffineDensityLogPowerMajorant_le_common
    {n : ℕ} {contourCoeff floor alpha delta x : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hx : 1 ≤ x)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha delta) :
    finiteAffineDensityLogPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope x ≤
      finiteAffineDensityCommonLogPower
        contourCoeff stripCoeff delta x := by
  have hx0 : 0 ≤ x := le_trans (by norm_num) hx
  have hcontourExponent : floor - alpha ≤ -delta := by
    linarith [certificate.contour]
  have hstripExponent :
      ∀ i, slope i * alpha - ceiling i ≤ -delta := by
    intro i
    linarith [certificate.strip i]
  have hpower : 0 ≤ x ^ (-delta) := Real.rpow_nonneg hx0 _
  have hlog : 0 ≤ (Real.log x) ^ (4 : ℕ) := by positivity
  have hlogFactor :
      1 ≤ 1 + (Real.log x) ^ (4 : ℕ) := by
    linarith
  have hlog_le_factor :
      (Real.log x) ^ (4 : ℕ) ≤
        1 + (Real.log x) ^ (4 : ℕ) := by
    linarith
  unfold finiteAffineDensityLogPowerMajorant
  calc
    contourCoeff * x ^ (floor - alpha) +
          ∑ i,
            stripCoeff i * x ^ (slope i * alpha - ceiling i) *
              (Real.log x) ^ (4 : ℕ) ≤
        contourCoeff * x ^ (-delta) *
            (1 + (Real.log x) ^ (4 : ℕ)) +
          ∑ i,
            stripCoeff i * x ^ (-delta) *
              (1 + (Real.log x) ^ (4 : ℕ)) := by
      apply add_le_add
      · have hcompressed :
            contourCoeff * x ^ (floor - alpha) ≤
              contourCoeff * x ^ (-delta) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le
              hx hcontourExponent)
            hcontourCoeff
        exact hcompressed.trans (by
          simpa using
            (mul_le_mul_of_nonneg_left
              hlogFactor (mul_nonneg hcontourCoeff hpower)))
      · apply Finset.sum_le_sum
        intro i _hi
        have hcompressed :
            stripCoeff i *
                x ^ (slope i * alpha - ceiling i) ≤
              stripCoeff i * x ^ (-delta) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le
              hx (hstripExponent i))
            (hstripCoeff i)
        have hwithLog :
            stripCoeff i *
                  x ^ (slope i * alpha - ceiling i) *
                (Real.log x) ^ (4 : ℕ) ≤
              stripCoeff i * x ^ (-delta) *
                (Real.log x) ^ (4 : ℕ) :=
          mul_le_mul_of_nonneg_right hcompressed hlog
        exact hwithLog.trans
          (mul_le_mul_of_nonneg_left
            hlog_le_factor
            (mul_nonneg (hstripCoeff i) hpower))
    _ =
        finiteAffineDensityCommonLogPower
          contourCoeff stripCoeff delta x := by
      unfold finiteAffineDensityCommonLogPower
      rw [finiteAffineDensityTotalCoeff, add_mul, Finset.sum_mul,
        add_mul, Finset.sum_mul]

/-- Every positive affine margin absorbs the common fourth logarithmic
factor. -/
theorem tendsto_finiteAffineDensityCommonLogPower_zero
    {n : ℕ} {contourCoeff delta : ℝ}
    {stripCoeff : Fin (n + 1) → ℝ}
    (hdelta : 0 < delta) :
    Tendsto
      (finiteAffineDensityCommonLogPower
        contourCoeff stripCoeff delta)
      atTop (nhds 0) := by
  have hpure :
      Tendsto (fun x : ℝ => x ^ (-delta))
        atTop (nhds 0) :=
    tendsto_rpow_neg_atTop hdelta
  have hlog :
      Tendsto
        (fun x : ℝ =>
          x ^ (-delta) * (Real.log x) ^ (4 : ℕ))
        atTop (nhds 0) := by
    exact tendsto_rpow_mul_log_four_atTop_nhds_zero
      (epsilon := delta / 2) (by linarith) (by linarith)
  have hsum :
      Tendsto
        (fun x : ℝ =>
          x ^ (-delta) *
            (1 + (Real.log x) ^ (4 : ℕ)))
        atTop (nhds 0) := by
    convert hpure.add hlog using 1
    · funext x
      ring
    · ring
  have hconstant :
      Tendsto
        (fun _ : ℝ =>
          finiteAffineDensityTotalCoeff contourCoeff stripCoeff)
        atTop
        (nhds (finiteAffineDensityTotalCoeff
          contourCoeff stripCoeff)) :=
    tendsto_const_nhds
  unfold finiteAffineDensityCommonLogPower
  simpa [mul_assoc] using hconstant.mul hsum

/-- A positive feasible affine margin makes the complete finite power-log
majorant tend to zero. -/
theorem tendsto_finiteAffineDensityLogPowerMajorant_zero
    {n : ℕ} {contourCoeff floor alpha delta : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hdelta : 0 < delta)
    (certificate :
      FiniteAffineDensityMarginCertificate
        floor ceiling slope alpha delta) :
    Tendsto
      (finiteAffineDensityLogPowerMajorant
        contourCoeff stripCoeff floor alpha ceiling slope)
      atTop (nhds 0) := by
  refine squeeze_zero' ?_ ?_
    (tendsto_finiteAffineDensityCommonLogPower_zero
      (contourCoeff := contourCoeff)
      (stripCoeff := stripCoeff)
      hdelta)
  · filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
    exact finiteAffineDensityLogPowerMajorant_nonneg
      hcontourCoeff hstripCoeff hx
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact finiteAffineDensityLogPowerMajorant_le_common
      hcontourCoeff hstripCoeff hx certificate

/-- Positive budget at the contour floor makes the optimally balanced finite
affine power-log majorant tend to zero automatically. -/
theorem tendsto_finiteAffineBalancedLogPowerMajorant_zero
    {n : ℕ} {contourCoeff floor : ℝ}
    {stripCoeff ceiling slope : Fin (n + 1) → ℝ}
    (hcontourCoeff : 0 ≤ contourCoeff)
    (hstripCoeff : ∀ i, 0 ≤ stripCoeff i)
    (hslope : ∀ i, 0 < slope i)
    (hbudget : ∀ i, slope i * floor < ceiling i) :
    Tendsto
      (finiteAffineDensityLogPowerMajorant
        contourCoeff stripCoeff floor
        (finiteAffineBalancedExponent floor ceiling slope)
        ceiling slope)
      atTop (nhds 0) := by
  exact tendsto_finiteAffineDensityLogPowerMajorant_zero
    hcontourCoeff hstripCoeff
    (finiteAffineOptimalMargin_pos
      floor ceiling slope hslope hbudget)
    (finiteAffineBalancedExponent_marginCertificate
      floor ceiling slope hslope)

end PrimeNumberTheorem
