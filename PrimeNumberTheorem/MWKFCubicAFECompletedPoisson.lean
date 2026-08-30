import PrimeNumberTheorem.MWKFCubicAFECompletedCutoff
import PrimeNumberTheorem.MWKFCubicAFEZeroMode

open Complex MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact zero/nonzero Poisson pairing for each added lower-scale box

All kernels are the actual finite-height physical kernels. The Fourier
series is absolutely summable before its zero term is removed. Adding a
lower-scale box changes neither positive integer progression, but generally
changes each separate mode. Only their sum is proved to vanish here.
-/

noncomputable def cubicAFECompletedFrequencyCoefficient
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) (h : ℤ) : ℂ :=
  (∫ t : ℝ, 𝓕 (cubicAFEProgressionCutoffSummand W T X V
    (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t)
      ((h : ℝ) / ((e / Nat.gcd d e : ℕ) : ℝ))) *
    Complex.exp (-2 * (Real.pi : ℂ) * I * (h : ℂ) * (δ : ℂ) *
      (Nat.gcdA (d / Nat.gcd d e) (e / Nat.gcd d e) : ℂ) /
        ((e / Nat.gcd d e : ℕ) : ℂ))

noncomputable def cubicAFECompletedFrequencyBox
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : ℤ,
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk h

noncomputable def cubicAFECompletedZeroModeBox
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk 0

noncomputable def cubicAFECompletedNonzeroModeBox
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : {h : ℤ // h ≠ 0},
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk h.val

theorem summable_cubicAFECompletedFrequencyCoefficient
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    Summable (cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk) := by
  have hq : 0 < Nat.gcd d e := by
    simpa only [Nat.gcd_comm] using Nat.gcd_pos_of_pos_left d he
  have hsN : e / Nat.gcd d e ≠ 0 := by
    intro hz
    have heq := (gcd_extraction hq.ne').2.1
    rw [hz, mul_zero] at heq
    exact he.ne' heq
  have hs : ((e / Nat.gcd d e : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hsN
  apply Summable.of_norm
  have hb := (summable_integral_cubicAFEProgressionFourier W hT hX V hd he
    (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) hs).norm
  apply hb.congr
  intro h
  unfold cubicAFECompletedFrequencyCoefficient
  rw [norm_mul, Complex.norm_exp]
  simp [Complex.mul_re, Complex.mul_im, Complex.div_re]

theorem cubicAFECompletedFrequencyBox_eq_progression
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    cubicAFECompletedFrequencyBox (d := d) W T X V he δ J jk =
      ∑' m : cubicAFEProgression d e δ, ∫ t : ℝ,
        cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t m.val := by
  unfold cubicAFECompletedFrequencyBox cubicAFECompletedFrequencyCoefficient
  simp_rw [integral_fourier_cubicAFEProgressionCutoffSummand W hT hX V hd he]
  exact (cubicAFEIntegratedProgression_poisson W hT hX V hd he _).symm

theorem cubicAFECompletedFrequencyCoefficient_zero
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J jk 0 =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t x := by
  simp only [cubicAFECompletedFrequencyCoefficient, Int.cast_zero, zero_div, mul_zero, zero_mul,
    Complex.exp_zero, mul_one, Real.fourier_real_eq_integral_exp_smul,
    Complex.ofReal_zero, one_smul]

private theorem zero_add_nonzero_tsum (f : ℤ → ℂ) (hf : Summable f) :
    f 0 + (∑' h : {h : ℤ // h ≠ 0}, f h.val) = ∑' h : ℤ, f h := by
  let e : {h : ℤ // h ≠ 0} ≃ {h : ℤ // h ∉ ({0} : Finset ℤ)} :=
    Equiv.subtypeEquivRight (fun h ↦ by simp)
  have heq : (∑' h : {h : ℤ // h ≠ 0}, f h.val) =
      ∑' h : {h : ℤ // h ∉ ({0} : Finset ℤ)}, f h.val :=
    e.tsum_eq (fun h ↦ f h.val)
  rw [heq]
  simpa only [Finset.sum_singleton] using hf.sum_add_tsum_subtype_compl ({0} : Finset ℤ)

theorem cubicAFECompletedFrequencyBox_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    cubicAFECompletedFrequencyBox (d := d) W T X V he δ J jk =
      cubicAFECompletedZeroModeBox (d := d) W T X V he δ J jk +
        cubicAFECompletedNonzeroModeBox (d := d) W T X V he δ J jk := by
  unfold cubicAFECompletedZeroModeBox cubicAFECompletedNonzeroModeBox
  rw [← mul_add, zero_add_nonzero_tsum _
    (summable_cubicAFECompletedFrequencyCoefficient W hT hX V hd he δ J jk)]
  rfl

/-- An added lower-scale box has zero full Poisson sum, not zero individual modes. -/
theorem cubicAFECompletedFrequencyBox_lower_scale
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ)
    {J : ℕ} {jk : ℕ × ℕ} (hjk : jk.1 < J ∨ jk.2 < J) :
    cubicAFECompletedFrequencyBox (d := d) W T X V he δ J jk = 0 := by
  rw [cubicAFECompletedFrequencyBox_eq_progression W hT hX V hd he δ J jk]
  have hz : ∀ m : cubicAFEProgression d e δ,
      cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2 m.val = 0 :=
    fun m ↦ cubicAFEProgressionCompletedCutoff_zero_on_progression he m.property hjk
  simp only [cubicAFEProgressionCutoffSummand, hz, Complex.ofReal_zero, zero_mul,
    integral_zero, tsum_zero]

/-- The complete physical zero-mode correction is canceled by nonzero frequencies,
with the exact 1/s Jacobian and inverse-residue phase on both sides. -/
theorem cubicAFECompletedLowerScale_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ)
    {J : ℕ} {jk : ℕ × ℕ} (hjk : jk.1 < J ∨ jk.2 < J) :
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∫ t : ℝ, ∫ x : ℝ, cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionCompletedCutoff (d := d) he δ J jk.1 jk.2) t x) +
    (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) *
      (∑' h : {h : ℤ // h ≠ 0}, cubicAFECompletedFrequencyCoefficient (d := d)
        W T X V he δ J jk h.val) = 0 := by
  have hh := cubicAFECompletedFrequencyBox_eq_zero_add_nonzero W hT hX V hd he δ J jk
  rw [cubicAFECompletedFrequencyBox_lower_scale W hT hX V hd he δ hjk] at hh
  simpa only [cubicAFECompletedZeroModeBox, cubicAFECompletedNonzeroModeBox,
    cubicAFECompletedFrequencyCoefficient_zero] using hh.symm

theorem cubicAFECompletedFrequencyCoefficient_shift
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) (h : ℤ) :
    cubicAFECompletedFrequencyCoefficient (d := d) W T X V he δ J (J + jk.1, J + jk.2) h =
      cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h := by
  have hc (t : ℝ) : cubicAFEProgressionCutoffSummand W T X V
      (cubicAFEProgressionCompletedCutoff (d := d) he δ J (J + jk.1) (J + jk.2)) t =
      cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t := by
    funext x
    unfold cubicAFEProgressionCutoffSummand
    rw [cubicAFEProgressionCompletedCutoff_shift]
  simp only [cubicAFECompletedFrequencyCoefficient, cubicAFEFrequencyCoefficient, hc]

theorem cubicAFECompletedFrequencyBox_shift
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (J : ℕ) (jk : ℕ × ℕ) :
    cubicAFECompletedFrequencyBox (d := d) W T X V he δ J (J + jk.1, J + jk.2) =
      cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk := by
  unfold cubicAFECompletedFrequencyBox
  simp_rw [cubicAFECompletedFrequencyCoefficient_shift]
  rfl

end PrimeNumberTheorem.MWKFCubic
