import PrimeNumberTheorem.MWKFCubicEulerSummability
import Mathlib.Analysis.Normed.Module.MultipliableUniformlyOn

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Local uniform convergence of the cubic Euler correction

The pointwise majorant from `MWKFCubicEulerSummability` is uniform throughout
an open real-part strip.  This file applies the product M-test without yet
claiming that the resulting three-variable product is holomorphic.
-/

/-- The open three-variable strip on which all real parts exceed `-eta`. -/
def mwkfEulerOpenStrip (eta : ℝ) : Set (ℂ × ℂ × ℂ) :=
  {z | -eta < z.1.re ∧ -eta < z.2.1.re ∧ -eta < z.2.2.re}

theorem isOpen_mwkfEulerOpenStrip (eta : ℝ) :
    IsOpen (mwkfEulerOpenStrip eta) := by
  have hs : IsOpen {z : ℂ × ℂ × ℂ | -eta < z.1.re} :=
    isOpen_lt continuous_const (by fun_prop)
  have ht : IsOpen {z : ℂ × ℂ × ℂ | -eta < z.2.1.re} :=
    isOpen_lt continuous_const (by fun_prop)
  have hw : IsOpen {z : ℂ × ℂ × ℂ | -eta < z.2.2.re} :=
    isOpen_lt continuous_const (by fun_prop)
  change IsOpen
    ({z : ℂ × ℂ × ℂ | -eta < z.1.re} ∩
      ({z | -eta < z.2.1.re} ∩ {z | -eta < z.2.2.re}))
  exact hs.inter (ht.inter hw)

/-- Every prime-local correction factor is continuous on the open strip. -/
theorem continuousOn_mwkfPrimeCorrectionFactor_openStrip
    (p : Nat.Primes) {eta : ℝ} (hetaHalf : eta < 1 / 2) :
    ContinuousOn
      (fun z : ℂ × ℂ × ℂ ↦
        mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2)
      (mwkfEulerOpenStrip eta) := by
  let A : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.1 + z.2.2))
  let B : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.2.1 + z.2.2))
  let C : ℂ × ℂ × ℂ → ℂ := fun z ↦
    (p : ℂ) ^ (-(1 + z.1 + z.2.1))
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast p.prop.ne_zero
  have hA : Continuous A := by
    dsimp [A]
    exact (continuous_id.const_cpow (Or.inl hp0)).comp (by fun_prop)
  have hB : Continuous B := by
    dsimp [B]
    exact (continuous_id.const_cpow (Or.inl hp0)).comp (by fun_prop)
  have hC : Continuous C := by
    dsimp [C]
    exact (continuous_id.const_cpow (Or.inl hp0)).comp (by fun_prop)
  have hden : ∀ z ∈ mwkfEulerOpenStrip eta,
      (1 - A z) * (1 - B z) ≠ 0 := by
    intro z hz
    have hza : -eta ≤ z.1.re := hz.1.le
    have hzb : -eta ≤ z.2.1.re := hz.2.1.le
    have hzc : -eta ≤ z.2.2.re := hz.2.2.le
    have hANe : 1 - A z ≠ 0 := by
      intro hzero
      have hAOne : A z = 1 := (sub_eq_zero.mp hzero).symm
      have hnorm : ‖A z‖ ≤ (p : ℝ) ^ (-1 + 2 * eta) := by
        simpa [A] using norm_prime_cpow_neg_one_add_le p.prop hza hzc
      rw [hAOne, norm_one] at hnorm
      have hpOne : (p : ℝ) ^ (-1 + 2 * eta) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith [hetaHalf])
      exact (not_le_of_gt hpOne) hnorm
    have hBNe : 1 - B z ≠ 0 := by
      intro hzero
      have hBOne : B z = 1 := (sub_eq_zero.mp hzero).symm
      have hnorm : ‖B z‖ ≤ (p : ℝ) ^ (-1 + 2 * eta) := by
        simpa [B] using norm_prime_cpow_neg_one_add_le p.prop hzb hzc
      rw [hBOne, norm_one] at hnorm
      have hpOne : (p : ℝ) ^ (-1 + 2 * eta) < 1 :=
        Real.rpow_lt_one_of_one_lt_of_neg
          (by exact_mod_cast p.prop.one_lt) (by linarith [hetaHalf])
      exact (not_le_of_gt hpOne) hnorm
    exact mul_ne_zero hANe hBNe
  change ContinuousOn
    (fun z : ℂ × ℂ × ℂ ↦
      (1 - A z - B z + C z) * (1 - C z) /
        ((1 - A z) * (1 - B z)))
    (mwkfEulerOpenStrip eta)
  exact (((continuous_const.sub hA).sub hB).add hC).mul
      (continuous_const.sub hC) |>.continuousOn.div
    ((continuous_const.sub hA).mul (continuous_const.sub hB) |>.continuousOn)
    hden

/-- For `eta < 1/4`, the prime-local correction product converges locally
uniformly throughout the corresponding open strip. -/
theorem hasProdLocallyUniformlyOn_mwkfPrimeCorrectionFactor
    {eta : ℝ} (hetaQuarter : eta < 1 / 4) :
    HasProdLocallyUniformlyOn
      (fun p : Nat.Primes ↦ fun z : ℂ × ℂ × ℂ ↦
        mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2)
      (fun z ↦ mwkfEulerCorrection z.1 z.2.1 z.2.2)
      (mwkfEulerOpenStrip eta) := by
  let alpha : ℝ := -1 + 2 * eta
  let q : ℝ := (2 : ℝ) ^ alpha
  let u : Nat.Primes → ℝ := fun p ↦
    4 / (1 - q) ^ 2 * ((p : ℝ) ^ alpha) ^ 2
  have halphaNeg : alpha < 0 := by
    dsimp [alpha]
    linarith
  have hdouble : 2 * alpha < -1 := by
    dsimp [alpha]
    linarith
  have hqOne : q < 1 := by
    dsimp [q]
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) halphaNeg
  have hu : Summable u := by
    dsimp [u]
    exact (summable_prime_rpow_sq hdouble).mul_left (4 / (1 - q) ^ 2)
  have hbound : ∀ᶠ p : Nat.Primes in Filter.cofinite,
      ∀ z ∈ mwkfEulerOpenStrip eta,
        ‖mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2 - 1‖ ≤ u p := by
    refine Filter.Eventually.of_forall ?_
    intro (p : Nat.Primes) z hz
    let rp : ℝ := (p : ℝ) ^ alpha
    have hpTwo : (2 : ℝ) ≤ p := by exact_mod_cast p.prop.two_le
    have hrpQ : rp ≤ q := by
      dsimp [rp, q]
      exact Real.rpow_le_rpow_of_nonpos (by norm_num) hpTwo halphaNeg.le
    have hrpOne : rp < 1 := hrpQ.trans_lt hqOne
    have hden : (1 - q) ^ 2 ≤ (1 - rp) ^ 2 := by
      rw [sq_le_sq₀ (sub_nonneg.mpr hqOne.le) (sub_nonneg.mpr hrpOne.le)]
      exact sub_le_sub_left hrpQ 1
    have hlocal :
        ‖mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2 - 1‖ ≤
          4 * rp ^ 2 / (1 - rp) ^ 2 := by
      simpa [alpha, rp] using
        (norm_mwkfPrimeCorrectionFactor_sub_one_le_on_strip
          (p := (p : ℕ)) p.prop (by linarith : eta < 1 / 2)
          hz.1.le hz.2.1.le hz.2.2.le)
    calc
      ‖mwkfPrimeCorrectionFactor p z.1 z.2.1 z.2.2 - 1‖ ≤
          4 * rp ^ 2 / (1 - rp) ^ 2 := hlocal
      _ ≤ 4 * rp ^ 2 / (1 - q) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity)
          (sq_pos_of_pos (sub_pos.mpr hqOne)) hden
      _ = u p := by
        dsimp [u, rp]
        ring
  have hprod := Summable.hasProdLocallyUniformlyOn_one_add
    (isOpen_mwkfEulerOpenStrip eta) hu hbound
    (fun p ↦ (continuousOn_mwkfPrimeCorrectionFactor_openStrip p
      (by linarith : eta < 1 / 2)).sub continuousOn_const)
  refine (hprod.congr ?_).congr_right ?_
  · intro S z hz
    apply Finset.prod_congr rfl
    intro p hp
    ring
  · intro z hz
    unfold mwkfEulerCorrection
    exact tprod_congr (fun _ ↦ by ring)

end PrimeNumberTheorem.MWKFCubic
