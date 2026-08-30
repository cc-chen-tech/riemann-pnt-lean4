import PrimeNumberTheorem.MWKFCubicAFEFrequencySummability

open Complex Filter MeasureTheory
open scoped FourierTransform

namespace PrimeNumberTheorem.MWKFCubic

/-!
# Exact zero/nonzero Fourier split in an actual dyadic box

Absolute convergence is proved before extracting the zero term. The zero
term is the actual physical double integral; no continuous lower-boundary
weight, Mellin weight or logarithmic phase is discarded.
-/

private theorem zero_add_nonzero_tsum (f : ℤ → ℂ) (hf : Summable f) :
    f 0 + (∑' h : {h : ℤ // h ≠ 0}, f h.val) = ∑' h : ℤ, f h := by
  let e : {h : ℤ // h ≠ 0} ≃ {h : ℤ // h ∉ ({0} : Finset ℤ)} :=
    Equiv.subtypeEquivRight (fun h ↦ by simp)
  have heq : (∑' h : {h : ℤ // h ≠ 0}, f h.val) =
      ∑' h : {h : ℤ // h ∉ ({0} : Finset ℤ)}, f h.val :=
    e.tsum_eq (fun h ↦ f h.val)
  rw [heq]
  simpa only [Finset.sum_singleton] using hf.sum_add_tsum_subtype_compl ({0} : Finset ℤ)

noncomputable def cubicAFEZeroModeBoxFinite
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk 0

noncomputable def cubicAFENonzeroModeBoxFinite
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) : ℂ :=
  (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∑' h : {h : ℤ // h ≠ 0},
    cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h.val

theorem summable_cubicAFENonzeroFrequencyCoefficient
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    Summable (fun h : {h : ℤ // h ≠ 0} ↦ cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h.val) :=
  (summable_cubicAFEFrequencyCoefficient W hT hX V hd he δ jk).subtype _

theorem cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk =
      cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk +
        cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk := by
  have hs := summable_cubicAFEFrequencyCoefficient W hT hX V hd he δ jk
  have hz : cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk 0 +
      (∑' h : {h : ℤ // h ≠ 0}, cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h.val) =
      ∑' h : ℤ, cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk h := by
    exact zero_add_nonzero_tsum _ hs
  unfold cubicAFEZeroModeBoxFinite cubicAFENonzeroModeBoxFinite
  rw [← mul_add, hz]
  rfl

theorem cubicAFEFrequencyCoefficient_zero
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) :
    cubicAFEFrequencyCoefficient (d := d) W T X V he δ jk 0 =
      ∫ t : ℝ, ∫ x : ℝ, cubicAFEProgressionCutoffSummand W T X V
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t x := by
  simp only [cubicAFEFrequencyCoefficient, Int.cast_zero, zero_div, mul_zero, zero_mul,
    Complex.exp_zero, mul_one, Real.fourier_real_eq_integral_exp_smul,
    Complex.ofReal_zero, one_smul]

/-- The Poisson zero mode still contains the full physical logarithmic
phase. Zero Fourier frequency does not mean zero original shift. -/
theorem cubicAFEZeroModeBoxFinite_eq_physicalIntegral
    (W : CubicTestWeight) (T X V : ℝ) {d e : ℕ} (he : 0 < e)
    (δ : ℤ) (jk : ℕ × ℕ) :
    cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ t : ℝ, ∫ x : ℝ,
        (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2 x : ℂ) *
          cubicAFEProgressionPhysicalSummand W T X V d e δ t x := by
  rw [cubicAFEZeroModeBoxFinite, cubicAFEFrequencyCoefficient_zero]
  rfl

/-- Fubini also identifies the zero mode with the space integral of the
actual time-integrated kernel, using the proved joint compact support. -/
theorem cubicAFEZeroModeBoxFinite_eq_integratedKernel
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (jk : ℕ × ℕ) :
    cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk =
      (((e / Nat.gcd d e : ℕ) : ℂ)⁻¹) * ∫ x : ℝ, ∫ t : ℝ,
        cubicAFEProgressionCutoffSummand W T X V
          (cubicAFEProgressionDyadicCutoff (d := d) he δ jk.1 jk.2) t x := by
  rw [cubicAFEZeroModeBoxFinite, cubicAFEFrequencyCoefficient_zero]
  congr 1
  exact integral_integral_swap_of_hasCompactSupport
    (continuous_cubicAFEProgressionCutoffSummand_joint W T X V hd he _ hX)
    (hasCompactSupport_cubicAFEProgressionCutoffSummand_joint W hT X V _)

/-- Finite families of whole boxes may be separated with no convergence
input beyond the actual per-box Fourier summability. Infinite separation
requires a separate zero-mode summability argument. -/
theorem sum_cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero
    (W : CubicTestWeight) {T : ℝ} (hT : T ≠ 0) {X : ℝ} (hX : 1 / 2 < X)
    (V : ℝ) {d e : ℕ} (hd : 0 < d) (he : 0 < e) (δ : ℤ) (J : Finset (ℕ × ℕ)) :
    (∑ jk ∈ J, cubicAFEFrequencyBoxFinite (d := d) W T X V he δ jk) =
      (∑ jk ∈ J, cubicAFEZeroModeBoxFinite (d := d) W T X V he δ jk) +
      (∑ jk ∈ J, cubicAFENonzeroModeBoxFinite (d := d) W T X V he δ jk) := by
  simp_rw [cubicAFEFrequencyBoxFinite_eq_zero_add_nonzero W hT hX V hd he δ]
  exact Finset.sum_add_distrib

end PrimeNumberTheorem.MWKFCubic
