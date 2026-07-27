import PrimeNumberTheorem.VKEdgePiOverTwoSweptL2

open Complex Filter MeasureTheory Set
open Asymptotics

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The ordinary logarithmic local second moment of the Chebyshev error. -/
def logarithmicPsiErrorSecondMoment (ε Y : ℝ) : ℝ :=
  ∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
    (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2

private theorem measurable_logarithmicPsiError :
    Measurable (fun y : ℝ =>
      chebyshevPsi (Real.exp y) - Real.exp y) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  fun_prop

private theorem logarithmicPsiError_abs_le_exp_growth (y : ℝ) :
    |chebyshevPsi (Real.exp y) - Real.exp y| ≤
      (Real.log 4 + 5) * Real.exp y := by
  have hpsi :
      chebyshevPsi (Real.exp y) ≤
        (Real.log 4 + 4) * Real.exp y := by
    rw [chebyshevPsi_eq_mathlib]
    exact Chebyshev.psi_le_const_mul_self (Real.exp_pos y).le
  have hpsiNonneg : 0 ≤ chebyshevPsi (Real.exp y) := by
    unfold chebyshevPsi
    exact Finset.sum_nonneg fun n _ => by
      rw [vonMangoldt_eq_mathlib]
      exact ArithmeticFunction.vonMangoldt_nonneg
  rw [abs_sub_le_iff]
  constructor
  · nlinarith [Real.exp_pos y]
  · nlinarith [Real.exp_pos y,
      Real.log_pos (by norm_num : 1 < (4 : ℝ))]

private theorem integrableOn_logarithmicPsiError_sq_Icc (a b : ℝ) :
    IntegrableOn
      (fun y : ℝ => (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2)
      (Set.Icc a b) := by
  let B : ℝ := ((Real.log 4 + 5) * Real.exp b) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      (measurable_logarithmicPsiError.pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hexp : Real.exp y ≤ Real.exp b :=
      Real.exp_le_exp.mpr hy.2
    have hcoef : 0 ≤ Real.log 4 + 5 := by positivity
    have habs :=
      logarithmicPsiError_abs_le_exp_growth y |>.trans
        (mul_le_mul_of_nonneg_left hexp hcoef)
    have hsq :
        (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [
        sq_abs (chebyshevPsi (Real.exp y) - Real.exp y),
        abs_nonneg (chebyshevPsi (Real.exp y) - Real.exp y)]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hsq

private theorem measurable_normalizedPsiError_arithmetic (rho : ℂ) :
    Measurable (normalizedPsiError rho) := by
  have hpsi : Measurable chebyshevPsi := by
    simpa only [chebyshevPsi_eq_mathlib] using
      Chebyshev.psi_mono.measurable
  unfold normalizedPsiError
  fun_prop

private theorem normalizedPsiError_abs_le_exp_growth_arithmetic
    (rho : ℂ) (y : ℝ) :
    |normalizedPsiError rho y| ≤
      ‖rho‖ * (Real.log 4 + 5) *
        Real.exp ((1 - rho.re) * y) := by
  unfold normalizedPsiError
  rw [abs_mul, abs_mul, abs_of_nonneg (norm_nonneg rho),
    abs_of_pos (Real.exp_pos _)]
  calc
    ‖rho‖ * |chebyshevPsi (Real.exp y) - Real.exp y| *
          Real.exp (-rho.re * y) ≤
        ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
          Real.exp (-rho.re * y) := by
      gcongr
      exact logarithmicPsiError_abs_le_exp_growth y
    _ = ‖rho‖ * (Real.log 4 + 5) *
          Real.exp ((1 - rho.re) * y) := by
      rw [show
          ‖rho‖ * ((Real.log 4 + 5) * Real.exp y) *
                Real.exp (-rho.re * y) =
              ‖rho‖ * (Real.log 4 + 5) *
                (Real.exp y * Real.exp (-rho.re * y)) by ring,
        ← Real.exp_add]
      congr 1
      ring_nf

private theorem integrableOn_normalizedPsiError_sq_Icc_arithmetic
    {rho : ℂ} (hrhoRe1 : rho.re < 1) (a b : ℝ) :
    IntegrableOn (fun y => normalizedPsiError rho y ^ 2)
      (Set.Icc a b) := by
  let B : ℝ :=
    (‖rho‖ * (Real.log 4 + 5) *
      Real.exp ((1 - rho.re) * b)) ^ 2
  apply IntegrableOn.of_bound isCompact_Icc.measure_lt_top
  · exact
      ((measurable_normalizedPsiError_arithmetic rho).pow_const 2
        |>.aestronglyMeasurable).restrict
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have hcoef : 0 ≤ 1 - rho.re := by linarith
    have hexp :
        Real.exp ((1 - rho.re) * y) ≤
          Real.exp ((1 - rho.re) * b) := by
      exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left hy.2 hcoef)
    have habs :=
      (normalizedPsiError_abs_le_exp_growth_arithmetic rho y).trans
        (mul_le_mul_of_nonneg_left hexp
          (mul_nonneg (norm_nonneg rho)
            (by positivity : 0 ≤ Real.log 4 + 5)))
    have hsq : normalizedPsiError rho y ^ 2 ≤ B := by
      dsimp [B]
      nlinarith [sq_abs (normalizedPsiError rho y),
        abs_nonneg (normalizedPsiError rho y)]
    rw [Real.norm_eq_abs,
      abs_of_nonneg (sq_nonneg (normalizedPsiError rho y))]
    exact hsq

/--
On a late logarithmic window, removing the normalizing exponential bounds
the normalized second moment by the ordinary Chebyshev-error moment.
-/
theorem normalizedPsiError_secondMoment_le_arithmetic
    {ε Y : ℝ} {rho : ℂ}
    (hε : 0 ≤ ε) (hY : 1 < Y)
    (hrhoRe0 : 0 ≤ rho.re) (hrhoRe1 : rho.re < 1) :
    (∫ y in Set.Icc (Real.log Y) ((1 + ε) * Real.log Y),
        normalizedPsiError rho y ^ 2) ≤
      ‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y) *
        logarithmicPsiErrorSecondMoment ε Y := by
  let a : ℝ := Real.log Y
  let b : ℝ := (1 + ε) * Real.log Y
  let c : ℝ := ‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y)
  have hlogPos : 0 < Real.log Y := Real.log_pos hY
  have hab : a ≤ b := by
    dsimp [a, b]
    nlinarith
  have hnormalizedInt :
      IntegrableOn (fun y => normalizedPsiError rho y ^ 2)
        (Set.Icc a b) :=
    integrableOn_normalizedPsiError_sq_Icc_arithmetic hrhoRe1 a b
  have hrawInt :
      IntegrableOn
        (fun y => (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2)
        (Set.Icc a b) :=
    integrableOn_logarithmicPsiError_sq_Icc a b
  have hmajorInt :
      IntegrableOn
        (fun y =>
          c * (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2)
        (Set.Icc a b) :=
    hrawInt.const_mul c
  have hpointwise :
      ∀ᵐ y ∂volume.restrict (Set.Icc a b),
        normalizedPsiError rho y ^ 2 ≤
          c * (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    have harg :
        -2 * rho.re * y ≤ -2 * rho.re * Real.log Y := by
      dsimp [a] at hy
      exact
        mul_le_mul_of_nonpos_left hy.1
          (mul_nonpos_of_nonpos_of_nonneg (by norm_num) hrhoRe0)
    have hexp :
        Real.exp (-2 * rho.re * y) ≤
          Real.exp (-2 * rho.re * Real.log Y) :=
      Real.exp_le_exp.mpr harg
    have hsquare :
        normalizedPsiError rho y ^ 2 =
          ‖rho‖ ^ 2 *
            (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
            Real.exp (-2 * rho.re * y) := by
      have hexpSquare :
          Real.exp (-rho.re * y) ^ 2 =
            Real.exp (-2 * rho.re * y) := by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring
      unfold normalizedPsiError
      calc
        (‖rho‖ * (chebyshevPsi (Real.exp y) - Real.exp y) *
            Real.exp (-rho.re * y)) ^ 2 =
          ‖rho‖ ^ 2 *
            (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
            Real.exp (-rho.re * y) ^ 2 := by ring
        _ = _ := by rw [hexpSquare]
    rw [hsquare]
    dsimp [c]
    have hnonneg :
        0 ≤ ‖rho‖ ^ 2 *
          (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 :=
      mul_nonneg (sq_nonneg _) (sq_nonneg _)
    calc
      ‖rho‖ ^ 2 *
            (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
            Real.exp (-2 * rho.re * y) ≤
          ‖rho‖ ^ 2 *
            (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 *
            Real.exp (-2 * rho.re * Real.log Y) :=
        mul_le_mul_of_nonneg_left hexp hnonneg
      _ = ‖rho‖ ^ 2 *
            Real.exp (-2 * rho.re * Real.log Y) *
            (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 := by ring
  change
    (∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2) ≤
      c * logarithmicPsiErrorSecondMoment ε Y
  calc
    (∫ y in Set.Icc a b, normalizedPsiError rho y ^ 2) ≤
        ∫ y in Set.Icc a b,
          c * (chebyshevPsi (Real.exp y) - Real.exp y) ^ 2 :=
      integral_mono_ae hnormalizedInt hmajorInt hpointwise
    _ = c * logarithmicPsiErrorSecondMoment ε Y := by
      rw [MeasureTheory.integral_const_mul]
      rfl

/--
An off-line zeta zero forces the ordinary Chebyshev-error second moment to
have scale `exp (2 * beta * log Y) * log Y` on every sufficiently late
epsilon logarithmic window.
-/
theorem exists_eventually_logarithmicPsiErrorSecondMoment_gt
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ∃ k : ℕ,
      riemannZeta (missingHarmonicContourCenter rho k) ≠ 0 ∧
      0 < centeredSharpenedSweptOrdinaryL2Constant ε rho k ∧
      ∀ᶠ Y : ℝ in Filter.atTop,
        (centeredSharpenedSweptOrdinaryL2Constant ε rho k /
              ‖rho‖ ^ 2) *
            Real.exp (2 * rho.re * Real.log Y) * Real.log Y <
          logarithmicPsiErrorSecondMoment ε Y := by
  have hrhoRe0 : 0 ≤ rho.re := by linarith
  have hrho : rho ≠ 0 := by
    exact ne_of_apply_ne Complex.im (by simpa using hgamma.ne')
  have hnormSqPos : 0 < ‖rho‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hrho)
  rcases
      exists_eventually_ordinarySecondMoment_in_epsilonLogWindow_gt_linear
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, hmissing, hconstantPos, hlower⟩
  refine ⟨k, hmissing, hconstantPos, ?_⟩
  filter_upwards [hlower, eventually_gt_atTop (1 : ℝ)] with
      Y hlowerY hY
  have hcomparison :=
    normalizedPsiError_secondMoment_le_arithmetic
      hε.le hY hrhoRe0 hrhoRe1
  have hcombined :
      centeredSharpenedSweptOrdinaryL2Constant ε rho k *
            Real.log Y <
        ‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y) *
          logarithmicPsiErrorSecondMoment ε Y :=
    hlowerY.trans_le hcomparison
  have hfactorPos :
      0 < ‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y) :=
    mul_pos hnormSqPos (Real.exp_pos _)
  have hquotient :
      (centeredSharpenedSweptOrdinaryL2Constant ε rho k *
            Real.log Y) /
          (‖rho‖ ^ 2 * Real.exp (-2 * rho.re * Real.log Y)) <
        logarithmicPsiErrorSecondMoment ε Y :=
    (div_lt_iff₀ hfactorPos).2 (by
      simpa [mul_comm] using hcombined)
  have hexpCancel :
      Real.exp (2 * rho.re * Real.log Y) *
          Real.exp (-(2 * rho.re * Real.log Y)) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    simp
  convert hquotient using 1
  field_simp [hnormSqPos.ne']
  calc
    Real.log Y * Real.exp (2 * rho.re * Real.log Y) *
          Real.exp (-(2 * rho.re * Real.log Y)) =
        Real.log Y *
          (Real.exp (2 * rho.re * Real.log Y) *
            Real.exp (-(2 * rho.re * Real.log Y))) := by ring
    _ = Real.log Y * 1 := by rw [hexpCancel]
    _ = Real.log Y := by ring

/--
Consequently the ordinary local second moment cannot be little-o of the
scale forced by an off-line zero. Any such upper bound would exclude that
zero.
-/
theorem logarithmicPsiErrorSecondMoment_not_isLittleO_of_offLineZero
    {ε : ℝ} {rho : ℂ} {sigma : ℝ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hzero : riemannZeta rho = 0)
    (hσ : 1 / 2 < sigma)
    (hσrho : sigma < rho.re)
    (hrhoRe1 : rho.re < 1) :
    ¬((fun Y : ℝ => logarithmicPsiErrorSecondMoment ε Y) =o[atTop]
      (fun Y : ℝ =>
        Real.exp (2 * rho.re * Real.log Y) * Real.log Y)) := by
  intro hsmall
  rcases
      exists_eventually_logarithmicPsiErrorSecondMoment_gt
        hε hgamma hzero hσ hσrho hrhoRe1 with
    ⟨k, _, hconstantPos, hlower⟩
  have hrho : rho ≠ 0 :=
    ne_of_apply_ne Complex.im (by simpa using hgamma.ne')
  have hnormSqPos : 0 < ‖rho‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr hrho)
  let c : ℝ :=
    centeredSharpenedSweptOrdinaryL2Constant ε rho k / ‖rho‖ ^ 2
  have hc : 0 < c := div_pos hconstantPos hnormSqPos
  have hsmallBound :
      ∀ᶠ Y : ℝ in atTop,
        ‖logarithmicPsiErrorSecondMoment ε Y‖ ≤
          (c / 2) *
            ‖Real.exp (2 * rho.re * Real.log Y) * Real.log Y‖ :=
    hsmall.def (half_pos hc)
  rcases eventually_atTop.mp hlower with ⟨A, hA⟩
  rcases eventually_atTop.mp hsmallBound with ⟨B, hB⟩
  let Y : ℝ := max (max A B) 2
  have hAY : A ≤ Y :=
    (le_max_left A B).trans (le_max_left (max A B) 2)
  have hBY : B ≤ Y :=
    (le_max_right A B).trans (le_max_left (max A B) 2)
  have hY : 1 < Y :=
    lt_of_lt_of_le (by norm_num) (le_max_right (max A B) 2)
  have hlowerY := hA Y hAY
  have hupperY := hB Y hBY
  have hlogPos : 0 < Real.log Y := Real.log_pos hY
  have hscalePos :
      0 < Real.exp (2 * rho.re * Real.log Y) * Real.log Y :=
    mul_pos (Real.exp_pos _) hlogPos
  have hmomentPos :
      0 < logarithmicPsiErrorSecondMoment ε Y := by
    exact
      (mul_pos hc hscalePos).trans
        (by simpa [c, mul_assoc] using hlowerY)
  rw [Real.norm_eq_abs, abs_of_pos hmomentPos,
      Real.norm_eq_abs, abs_of_pos hscalePos] at hupperY
  have hlowerY' :
      c * (Real.exp (2 * rho.re * Real.log Y) * Real.log Y) <
        logarithmicPsiErrorSecondMoment ε Y := by
    simpa [c, mul_assoc] using hlowerY
  nlinarith

/--
Direct zero-exclusion form: a local mean-square upper bound strictly below
the scale attached to `rho.re` rules out a zeta zero at `rho`.
-/
theorem riemannZeta_ne_zero_of_logarithmicPsiErrorSecondMoment_isLittleO
    {ε : ℝ} {rho : ℂ}
    (hε : 0 < ε)
    (hgamma : 0 < rho.im)
    (hrhoReHalf : 1 / 2 < rho.re)
    (hrhoRe1 : rho.re < 1)
    (hsmall :
      (fun Y : ℝ => logarithmicPsiErrorSecondMoment ε Y) =o[atTop]
        (fun Y : ℝ =>
          Real.exp (2 * rho.re * Real.log Y) * Real.log Y)) :
    riemannZeta rho ≠ 0 := by
  intro hzero
  let sigma : ℝ := (1 / 2 + rho.re) / 2
  have hσ : 1 / 2 < sigma := by
    dsimp [sigma]
    linarith
  have hσrho : sigma < rho.re := by
    dsimp [sigma]
    linarith
  exact
    (logarithmicPsiErrorSecondMoment_not_isLittleO_of_offLineZero
      hε hgamma hzero hσ hσrho hrhoRe1) hsmall

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
