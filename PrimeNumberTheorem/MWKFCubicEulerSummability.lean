import PrimeNumberTheorem.MWKFCubicEulerCorrection
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.SumPrimeReciprocals

open scoped BigOperators

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Summability of the cubic Euler correction over primes

The quadratic local estimate is summed over `Nat.Primes`.  The strict strip
threshold `eta < 1/4` is exactly what makes the majorant exponent
`-2 + 4 * eta` smaller than `-1`.
-/

/-- Squaring a prime real power preserves summability whenever the doubled
exponent is below `-1`. -/
theorem summable_prime_rpow_sq
    {alpha : ℝ} (halpha : 2 * alpha < -1) :
    Summable (fun p : Nat.Primes ↦ ((p : ℝ) ^ alpha) ^ 2) := by
  refine (Nat.Primes.summable_rpow.mpr halpha).congr ?_
  intro p
  simpa [mul_comm] using
    (Real.rpow_mul_natCast (x := (p : ℝ)) (by positivity) alpha 2)

/-- On every fixed symmetric strip of radius `eta < 1/4`, the norms of the
prime-local correction errors form a summable series. -/
theorem summable_norm_mwkfPrimeCorrectionFactor_sub_one_on_strip
    {s t w : ℂ} {eta : ℝ}
    (hetaQuarter : eta < 1 / 4)
    (hs : -eta ≤ s.re) (ht : -eta ≤ t.re) (hw : -eta ≤ w.re) :
    Summable (fun p : Nat.Primes ↦
      ‖mwkfPrimeCorrectionFactor p s t w - 1‖) := by
  let alpha : ℝ := -1 + 2 * eta
  let q : ℝ := (2 : ℝ) ^ alpha
  let K : ℝ := 4 / (1 - q) ^ 2
  have halphaNeg : alpha < 0 := by
    dsimp [alpha]
    linarith
  have hdouble : 2 * alpha < -1 := by
    dsimp [alpha]
    linarith
  have hqOne : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) halphaNeg
  have hsum : Summable (fun p : Nat.Primes ↦ K * ((p : ℝ) ^ alpha) ^ 2) :=
    (summable_prime_rpow_sq hdouble).mul_left K
  refine hsum.of_nonneg_of_le (fun _ ↦ norm_nonneg _) ?_
  intro p
  let rp : ℝ := (p : ℝ) ^ alpha
  have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
  have hrpNonneg : 0 ≤ rp := by
    dsimp [rp]
    exact Real.rpow_nonneg (by positivity) _
  have hrpQ : rp ≤ q := by
    dsimp [rp, q]
    exact Real.rpow_le_rpow_of_nonpos (by norm_num) hpTwo halphaNeg.le
  have hrpOne : rp < 1 := hrpQ.trans_lt hqOne
  have hqDenNonneg : 0 ≤ 1 - q := sub_nonneg.mpr hqOne.le
  have hrpDenNonneg : 0 ≤ 1 - rp := sub_nonneg.mpr hrpOne.le
  have hden : (1 - q) ^ 2 ≤ (1 - rp) ^ 2 := by
    rw [sq_le_sq₀ hqDenNonneg hrpDenNonneg]
    exact sub_le_sub_left hrpQ 1
  have hlocal :
      ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
        4 * rp ^ 2 / (1 - rp) ^ 2 := by
    simpa [alpha, rp] using
      (norm_mwkfPrimeCorrectionFactor_sub_one_le_on_strip
        (p := (p : ℕ)) p.prop (by linarith : eta < 1 / 2) hs ht hw)
  calc
    ‖mwkfPrimeCorrectionFactor p s t w - 1‖ ≤
        4 * rp ^ 2 / (1 - rp) ^ 2 := hlocal
    _ ≤ 4 * rp ^ 2 / (1 - q) ^ 2 :=
      div_le_div_of_nonneg_left (by positivity)
        (sq_pos_of_pos (sub_pos.mpr hqOne)) hden
    _ = K * ((p : ℝ) ^ alpha) ^ 2 := by
      dsimp [K, rp]
      ring

/-- The prime-local correction factors form a convergent unordered product at
every point of the strict strip `eta < 1/4`. -/
theorem multipliable_mwkfPrimeCorrectionFactor_on_strip
    {s t w : ℂ} {eta : ℝ}
    (hetaQuarter : eta < 1 / 4)
    (hs : -eta ≤ s.re) (ht : -eta ≤ t.re) (hw : -eta ≤ w.re) :
    Multipliable (fun p : Nat.Primes ↦ mwkfPrimeCorrectionFactor p s t w) := by
  have h := multipliable_one_add_of_summable
    (summable_norm_mwkfPrimeCorrectionFactor_sub_one_on_strip
      hetaQuarter hs ht hw)
  exact h.congr (fun _ ↦ by ring)

/-- The global cubic Euler correction, defined as the unordered product of its
prime-local factors. -/
noncomputable def mwkfEulerCorrection (s t w : ℂ) : ℂ :=
  ∏' p : Nat.Primes, mwkfPrimeCorrectionFactor p s t w

/-- On the strict strip `eta < 1/4`, the defining prime product converges to
`mwkfEulerCorrection`. -/
theorem hasProd_mwkfPrimeCorrectionFactor_on_strip
    {s t w : ℂ} {eta : ℝ}
    (hetaQuarter : eta < 1 / 4)
    (hs : -eta ≤ s.re) (ht : -eta ≤ t.re) (hw : -eta ≤ w.re) :
    HasProd (fun p : Nat.Primes ↦ mwkfPrimeCorrectionFactor p s t w)
      (mwkfEulerCorrection s t w) := by
  exact (multipliable_mwkfPrimeCorrectionFactor_on_strip
    hetaQuarter hs ht hw).hasProd

/-- At the center of the Perron expansion the global correction product is
exactly one. -/
theorem mwkfEulerCorrection_zero : mwkfEulerCorrection 0 0 0 = 1 := by
  rw [mwkfEulerCorrection,
    tprod_congr (fun p : Nat.Primes ↦ mwkfPrimeCorrectionFactor_zero p.prop)]
  exact tprod_one

end PrimeNumberTheorem.MWKFCubic
