import HardyTheorem.AFECriticalDyadicProductWindow
import MathlibAux.RealDyadicScale

/-!
# Absorb the critical AFE remainder at the half-range mollifier scale

The canonical square-root AFE remainder contributes a factor
`X * L^(-1/2)` after multiplication by a mollifier of length `X`.  This
module records the exact power saving when `X <= L^(9/20)`.
-/

namespace HardyTheorem
namespace AFE

/-- Choose the first dyadic power above a real scale.  Besides the strict
upper coverage needed by the AFE cutoff, the selected power is at most twice
the original scale. -/
theorem exists_dyadic_strict_upper_le_two_mul {r : ℝ} (hr : 1 ≤ r) :
    ∃ K : ℕ, r < (((2 ^ K : ℕ) : ℝ)) ∧
      (((2 ^ K : ℕ) : ℝ)) ≤ 2 * r := by
  obtain ⟨j, hjlow, hjhigh⟩ :=
    MathlibAux.exists_nat_pow_two_le_lt_pow_two hr
  refine ⟨j + 1, ?_, ?_⟩
  · simpa only [Nat.cast_pow, Nat.cast_ofNat] using hjhigh
  · norm_num only [pow_succ, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    nlinarith [hjlow]

/-- At any mollifier length `X <= L^(9/20)`, the squared canonical AFE
remainder is at most `4 R^2 L^(-1/20)`. -/
theorem criticalAfeRemainderWindowBound_le_halfRange
    {R L : ℝ} {X : ℕ} (hL : 1 ≤ L)
    (hX : (X : ℝ) ≤ L ^ (9 / 20 : ℝ)) :
    criticalAfeRemainderWindowBound R L X ≤
      4 * R ^ 2 * L ^ (-1 / 20 : ℝ) := by
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hsqrt : (Real.sqrt X) ^ 2 = (X : ℝ) :=
    Real.sq_sqrt (Nat.cast_nonneg X)
  have hpow : (L ^ (-1 / 4 : ℝ)) ^ 2 = L ^ (-1 / 2 : ℝ) := by
    rw [pow_two, ← Real.rpow_add hLpos]
    congr 1
    norm_num
  rw [criticalAfeRemainderWindowBound]
  calc
    (R * L ^ (-1 / 4 : ℝ) * (2 * Real.sqrt X)) ^ 2 =
        4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * (X : ℝ) := by
      rw [mul_pow, mul_pow, hpow]
      calc
        R ^ 2 * L ^ (-1 / 2 : ℝ) * (2 * Real.sqrt X) ^ 2 =
            4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * (Real.sqrt X) ^ 2 := by ring
        _ = 4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * (X : ℝ) := by rw [hsqrt]
    _ ≤ 4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ) := by
      gcongr
    _ = 4 * R ^ 2 * L ^ (-1 / 20 : ℝ) := by
      calc
        4 * R ^ 2 * L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ) =
            4 * R ^ 2 *
              (L ^ (-1 / 2 : ℝ) * L ^ (9 / 20 : ℝ)) := by ring
        _ = 4 * R ^ 2 * L ^ ((-1 / 2 : ℝ) + 9 / 20) := by
          rw [Real.rpow_add hLpos]
        _ = 4 * R ^ 2 * L ^ (-1 / 20 : ℝ) := by norm_num

/-- Since `L >= 1`, the half-range remainder is uniformly bounded by
`4 R^2`; its stronger `L^(-1/20)` decay is retained by the preceding
theorem. -/
theorem criticalAfeRemainderWindowBound_le_halfRange_const
    {R L : ℝ} {X : ℕ} (hL : 1 ≤ L)
    (hX : (X : ℝ) ≤ L ^ (9 / 20 : ℝ)) :
    criticalAfeRemainderWindowBound R L X ≤ 4 * R ^ 2 := by
  calc
    criticalAfeRemainderWindowBound R L X ≤
        4 * R ^ 2 * L ^ (-1 / 20 : ℝ) :=
      criticalAfeRemainderWindowBound_le_halfRange hL hX
    _ ≤ 4 * R ^ 2 * 1 := by
      gcongr
      exact Real.rpow_le_one_of_one_le_of_nonpos hL (by norm_num)
    _ = 4 * R ^ 2 := by ring

/-- The complete conditional critical-line window bound with the AFE
remainder already normalized at the half-range scale.  The only analytic
premise is still the explicit symmetric square-root AFE target. -/
theorem setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {K X : ℕ} {L U Delta : ℝ},
      1 < L → 2 ≤ X →
      (X : ℝ) ≤ L ^ (9 / 20 : ℝ) →
      Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ)) →
      2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta →
      ∀ w : ℝ,
      (∫ t : ℝ in Set.Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + Complex.I * t))) ≤
        3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              (4 * R ^ 2 * L ^ (-1 / 20 : ℝ))) := by
  obtain ⟨R, hR, hwindow⟩ :=
    setIntegral_gaussian_normSq_criticalAfeProduct_le_of_dyadic_target hAFE
  refine ⟨R, hR, ?_⟩
  intro K X L U Delta hL hX hXscale hU hDelta w
  have hbase := hwindow hL hX hU hDelta w
  have hrem := criticalAfeRemainderWindowBound_le_halfRange
    (R := R) hL.le hXscale
  calc
    (∫ t : ℝ in Set.Icc L U,
        Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
          Complex.normSq
            (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
              selbergMoebiusMollifier X
                ((1 / 2 : ℂ) + Complex.I * t))) ≤
        3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              criticalAfeRemainderWindowBound R L X) := hbase
    _ ≤ 3 *
          (2 * dyadicCriticalGaussianBound K X Delta +
            Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
              (4 * R ^ 2 * L ^ (-1 / 20 : ℝ))) := by
      gcongr

/-- A parameter-ready form of the half-range critical estimate.  The
dyadic depth is chosen internally.  The single scale condition
`4 * sqrt(U/(2*pi)) * X <= Delta` implies the polynomial separation
condition because the selected dyadic cutoff is at most twice the
square-root scale. -/
theorem exists_dyadic_setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange
    (hAFE : zeta_critical_afe_target) :
    ∃ R > (0 : ℝ), ∀ {X : ℕ} {L U Delta : ℝ},
      1 < L → 2 ≤ X →
      (X : ℝ) ≤ L ^ (9 / 20 : ℝ) →
      1 ≤ Real.sqrt (U / (2 * Real.pi)) →
      4 * Real.sqrt (U / (2 * Real.pi)) * (X : ℝ) ≤ Delta →
      ∀ w : ℝ, ∃ K : ℕ,
        Real.sqrt (U / (2 * Real.pi)) < (((2 ^ K : ℕ) : ℝ)) ∧
        (((2 ^ K : ℕ) : ℝ)) ≤
          2 * Real.sqrt (U / (2 * Real.pi)) ∧
        (∫ t : ℝ in Set.Icc L U,
          Real.exp (-((t - w) ^ 2) / Delta ^ 2) *
            Complex.normSq
              (riemannZeta ((1 / 2 : ℂ) + Complex.I * t) *
                selbergMoebiusMollifier X
                  ((1 / 2 : ℂ) + Complex.I * t))) ≤
          3 *
            (2 * dyadicCriticalGaussianBound K X Delta +
              Real.sqrt (Real.pi / (1 / Delta ^ 2)) *
                (4 * R ^ 2 * L ^ (-1 / 20 : ℝ))) := by
  obtain ⟨R, hR, hwindow⟩ :=
    setIntegral_gaussian_normSq_criticalAfeProduct_le_halfRange hAFE
  refine ⟨R, hR, ?_⟩
  intro X L U Delta hL hX hXscale hUsqrt hDelta w
  obtain ⟨K, hKlower, hKupper⟩ :=
    exists_dyadic_strict_upper_le_two_mul hUsqrt
  have hseparation : 2 * (((2 ^ K * X : ℕ) : ℝ)) ≤ Delta := by
    calc
      2 * (((2 ^ K * X : ℕ) : ℝ)) =
          2 * (((2 ^ K : ℕ) : ℝ)) * (X : ℝ) := by
        rw [Nat.cast_mul]
        ring
      _ ≤ 2 * (2 * Real.sqrt (U / (2 * Real.pi))) * (X : ℝ) := by
        gcongr
      _ = 4 * Real.sqrt (U / (2 * Real.pi)) * (X : ℝ) := by ring
      _ ≤ Delta := hDelta
  exact ⟨K, hKlower, hKupper,
    hwindow hL hX hXscale hKlower hseparation w⟩

end AFE
end HardyTheorem
