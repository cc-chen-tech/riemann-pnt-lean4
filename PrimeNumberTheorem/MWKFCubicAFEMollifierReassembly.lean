import PrimeNumberTheorem.MWKFCubicAFECombinedPhase

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace MWKFCubic

/-!
# Finite-height reassembly of the cubic AFE with the finite mollifier

This file keeps the AFE height `V` finite.  In particular, the pointwise
limit below is not interchanged with the outer `t`-integral.
-/

/-- The finite-height AFE approximation to the complete mollified integrand. -/
noncomputable def cubicAFEMollifiedApproximation
    (W : CubicTestWeight) (T X V t : ℝ) : ℂ :=
  (2 * cubicAFEDoubleSumFinite t X V) *
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ) *
    (W (t / T) : ℂ)

/-- The contribution of one ordered mollifier pair before expanding the AFE
double Dirichlet series. -/
noncomputable def cubicAFEMollifierPairApproximation
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ) (t : ℝ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) *
    (cubicMollifierCoefficient T e : ℂ) *
    ((2 * cubicAFEDoubleSumFinite t X V) *
      ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
        (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t)) *
      (W (t / T) : ℂ))

/-- At each physical height `t`, the finite-height mollified AFE converges to
the literal integrand.  No limit--integral interchange is asserted here. -/
theorem tendsto_cubicAFEMollifiedApproximation
    (W : CubicTestWeight) (T t : ℝ) {X : ℝ} (hX : 1 / 2 < X) :
    Tendsto (fun V : ℝ ↦ cubicAFEMollifiedApproximation W T X V t)
      atTop (nhds (cubicMomentIntegrand W T t : ℂ)) := by
  have h := (tendsto_two_mul_cubicAFEDoubleSumFinite t hX).mul_const
    (Complex.normSq (HardyTheorem.selbergMoebiusMollifier
      (cubicMollifierLength T) (cubicCriticalPoint t)) : ℂ)
  have h' := h.mul_const (W (t / T) : ℂ)
  simpa [cubicAFEMollifiedApproximation, cubicMomentIntegrand,
    cubicCriticalPoint] using h'

/-- Exact finite `(d,e)` reassembly of the finite-height mollified AFE. -/
theorem cubicAFEMollifiedApproximation_eq_pairSum
    (W : CubicTestWeight) (T X V t : ℝ) :
    cubicAFEMollifiedApproximation W T X V t =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        cubicAFEMollifierPairApproximation W T X V d e t := by
  unfold cubicAFEMollifiedApproximation cubicAFEMollifierPairApproximation
  rw [show cubicCriticalPoint t = (1 / 2 : ℂ) + I * t by rfl,
    cubicMollifierNormSq_eq_doubleSum]
  simp only [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  ring

/-- Absolute summability of the finite-height AFE weights.  This is inherited
from the dominated-convergence `HasSum` before the vertical integral was
normalized. -/
theorem summable_cubicAFEWeightFinite
    (t : ℝ) {X : ℝ} (hX : 1 / 2 < X) (V : ℝ) :
    Summable (fun p : ℕ × ℕ ↦ cubicAFEWeightFinite t X V p) := by
  have h :=
    (hasSum_intervalIntegral_cubicAFENormalizedDirichletTerm t hX V).mul_left
      (1 / (2 * Real.pi) : ℂ)
  simpa only [cubicAFEWeightFinite] using h.summable

/-- One fully expanded `(p,d,e)` term, with the exact combined arithmetic
factor and the product-only Mellin weight kept separate. -/
noncomputable def cubicAFECombinedSummandFinite
    (W : CubicTestWeight) (T X V : ℝ) (d e : ℕ)
    (t : ℝ) (p : ℕ × ℕ) : ℂ :=
  (cubicMollifierCoefficient T d : ℂ) *
    (cubicMollifierCoefficient T e : ℂ) * 2 *
    (cubicAFECombinedArithmeticFactor t p d e *
      cubicAFEProductWeightFinite t X V (cubicAFEPositiveIndexProduct p)) *
    (W (t / T) : ℂ)

theorem summable_cubicAFECombinedSummandFinite
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (t : ℝ) :
    Summable (fun p : ℕ × ℕ ↦
      cubicAFECombinedSummandFinite W T X V d e t p) := by
  let C : ℂ :=
    (cubicMollifierCoefficient T d : ℂ) *
      (cubicMollifierCoefficient T e : ℂ) * 2
  have hsum := summable_cubicAFEWeightFinite t hX V
  have hfun :
      (fun p : ℕ × ℕ ↦
        cubicAFECombinedSummandFinite W T X V d e t p) =
      fun p : ℕ × ℕ ↦
        C * cubicAFEWeightFinite t X V p *
          ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
            (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t)) *
          (W (t / T) : ℂ) := by
    funext p
    rw [cubicAFEWeightFinite_eq_arithmetic_mul_productWeight]
    unfold cubicAFECombinedSummandFinite cubicAFECombinedArithmeticFactor C
    ring
  rw [hfun]
  exact (((hsum.mul_left C).mul_right
    ((1 / (d : ℂ) ^ cubicCriticalPoint t) *
      (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t))).mul_right
        (W (t / T) : ℂ))

/-- Each ordered mollifier-pair approximation is exactly the absolutely
convergent sum of its fully exposed `(p,d,e)` terms. -/
theorem cubicAFEMollifierPairApproximation_eq_tsum
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) (d e : ℕ) (t : ℝ) :
    cubicAFEMollifierPairApproximation W T X V d e t =
      ∑' p : ℕ × ℕ,
        cubicAFECombinedSummandFinite W T X V d e t p := by
  have _hsum :=
    summable_cubicAFECombinedSummandFinite W T hX V d e t
  let C : ℂ :=
    (cubicMollifierCoefficient T d : ℂ) *
      (cubicMollifierCoefficient T e : ℂ) * 2
  let P : ℂ :=
    (1 / (d : ℂ) ^ cubicCriticalPoint t) *
      (starRingEnd ℂ) (1 / (e : ℂ) ^ cubicCriticalPoint t)
  let Z : ℂ := ∑' p : ℕ × ℕ,
    cubicAFEDirichletTerm t 0 p *
      cubicAFEProductWeightFinite t X V (cubicAFEPositiveIndexProduct p)
  have hZ : cubicAFEDoubleSumFinite t X V = Z := by
    unfold cubicAFEDoubleSumFinite Z
    apply tsum_congr
    intro p
    exact cubicAFEWeightFinite_eq_arithmetic_mul_productWeight t X V p
  have hinner :
      (∑' p : ℕ × ℕ,
        cubicAFECombinedArithmeticFactor t p d e *
          cubicAFEProductWeightFinite t X V
            (cubicAFEPositiveIndexProduct p)) = Z * P := by
    calc
      (∑' p : ℕ × ℕ,
          cubicAFECombinedArithmeticFactor t p d e *
            cubicAFEProductWeightFinite t X V
              (cubicAFEPositiveIndexProduct p)) =
          ∑' p : ℕ × ℕ,
            (cubicAFEDirichletTerm t 0 p *
              cubicAFEProductWeightFinite t X V
                (cubicAFEPositiveIndexProduct p)) * P := by
            apply tsum_congr
            intro p
            unfold cubicAFECombinedArithmeticFactor P
            ring
      _ = Z * P := by rw [tsum_mul_right]
  have hpair :
      cubicAFEMollifierPairApproximation W T X V d e t =
        C * (Z * P) * (W (t / T) : ℂ) := by
    unfold cubicAFEMollifierPairApproximation C P
    rw [hZ]
    ring
  have hrhs :
      (∑' p : ℕ × ℕ,
        cubicAFECombinedSummandFinite W T X V d e t p) =
      C * (∑' p : ℕ × ℕ,
        cubicAFECombinedArithmeticFactor t p d e *
          cubicAFEProductWeightFinite t X V
            (cubicAFEPositiveIndexProduct p)) * (W (t / T) : ℂ) := by
    calc
      (∑' p : ℕ × ℕ,
        cubicAFECombinedSummandFinite W T X V d e t p) =
          ∑' p : ℕ × ℕ,
            C * (cubicAFECombinedArithmeticFactor t p d e *
              cubicAFEProductWeightFinite t X V
                (cubicAFEPositiveIndexProduct p)) * (W (t / T) : ℂ) := by
              apply tsum_congr
              intro p
              unfold cubicAFECombinedSummandFinite C
              ring
      _ = C * (∑' p : ℕ × ℕ,
          cubicAFECombinedArithmeticFactor t p d e *
            cubicAFEProductWeightFinite t X V
              (cubicAFEPositiveIndexProduct p)) * (W (t / T) : ℂ) := by
            rw [tsum_mul_right, tsum_mul_left]
  calc
    cubicAFEMollifierPairApproximation W T X V d e t =
        C * (Z * P) * (W (t / T) : ℂ) := hpair
    _ = C * (∑' p : ℕ × ℕ,
        cubicAFECombinedArithmeticFactor t p d e *
          cubicAFEProductWeightFinite t X V
            (cubicAFEPositiveIndexProduct p)) * (W (t / T) : ℂ) := by
          rw [hinner]
    _ = ∑' p : ℕ × ℕ,
        cubicAFECombinedSummandFinite W T X V d e t p := hrhs.symm

/-- The complete finite-height mollified AFE as a finite `(d,e)` sum of
absolutely convergent `p`-sums. -/
theorem cubicAFEMollifiedApproximation_eq_tripleSum
    (W : CubicTestWeight) (T : ℝ) {X : ℝ} (hX : 1 / 2 < X)
    (V t : ℝ) :
    cubicAFEMollifiedApproximation W T X V t =
      ∑ d ∈ cubicMollifierSupport T, ∑ e ∈ cubicMollifierSupport T,
        ∑' p : ℕ × ℕ,
          cubicAFECombinedSummandFinite W T X V d e t p := by
  rw [cubicAFEMollifiedApproximation_eq_pairSum]
  apply Finset.sum_congr rfl
  intro d hd
  apply Finset.sum_congr rfl
  intro e he
  exact cubicAFEMollifierPairApproximation_eq_tsum W T hX V d e t

/-- Fully exposed amplitude and oscillatory phase of one combined summand. -/
theorem cubicAFECombinedSummandFinite_eq_exp
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}
    (hd : d ≠ 0) (he : e ≠ 0) (t : ℝ) (p : ℕ × ℕ) :
    cubicAFECombinedSummandFinite W T X V d e t p =
      (cubicMollifierCoefficient T d : ℂ) *
        (cubicMollifierCoefficient T e : ℂ) * 2 *
        (((((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹)) *
          Complex.exp
            ((I * (cubicAFECombinedLogPhase p d e : ℂ)) * t) *
          cubicAFEProductWeightFinite t X V
            (cubicAFEPositiveIndexProduct p)) *
        (W (t / T) : ℂ) := by
  unfold cubicAFECombinedSummandFinite
  rw [cubicAFECombinedArithmeticFactor_eq_exp t p hd he]

/-- On the exact multiplicative diagonal the fully expanded combined summand
has no oscillatory exponential. -/
theorem cubicAFECombinedSummandFinite_eq_on_diagonal
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ}
    (hd : 0 < d) (he : 0 < e) (t : ℝ) (p : ℕ × ℕ)
    (hdiag : (p.2 + 1) * e = (p.1 + 1) * d) :
    cubicAFECombinedSummandFinite W T X V d e t p =
      (cubicMollifierCoefficient T d : ℂ) *
        (cubicMollifierCoefficient T e : ℂ) * 2 *
        (((Real.sqrt (cubicAFEPositiveIndexProduct p) : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt (d * e) : ℝ) : ℂ)⁻¹ *
          cubicAFEProductWeightFinite t X V
            (cubicAFEPositiveIndexProduct p)) *
        (W (t / T) : ℂ) := by
  unfold cubicAFECombinedSummandFinite
  rw [cubicAFECombinedArithmeticFactor_eq_on_diagonal t p hd he hdiag]

end MWKFCubic
end PrimeNumberTheorem
