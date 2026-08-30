import PrimeNumberTheorem.CarlsonDetectorCount
import PrimeNumberTheorem.CarlsonTwoScaleFarRight

/-! Finite rectangle-zero support and vertical boundary selection for the
two-scale detector.  The nontriviality input is the proved far-right bound,
not an assumed discrete-zero set. -/

open Complex Set

namespace PrimeNumberTheorem.CarlsonZeroDensity

noncomputable def regularizedTwoScaleCarlsonRectangleDivisorSupport
    (Y0 Y1 : ℕ) (sigma alpha a b : ℝ) : Finset ℂ :=
  ((MeromorphicOn.divisor (regularizedTwoScaleCarlsonZeroDetector Y0 Y1)
      (carlsonDetectorRectangle sigma alpha a b)).finiteSupport
    (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset

/-- On a rectangle in the right half-plane, finite divisor support is
exactly the actual zero set of the regularized two-scale detector. -/
theorem mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma alpha a b : ℝ} (hsigma : 0 < sigma) {z : ℂ}
    (hz : z ∈ carlsonDetectorRectangle sigma alpha a b) :
    z ∈ regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 sigma alpha a b ↔
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 z = 0 := by
  classical
  let U := carlsonDetectorRectangle sigma alpha a b
  let f := regularizedTwoScaleCarlsonZeroDetector Y0 Y1
  let D := MeromorphicOn.divisor f U
  have hf : AnalyticOnNhd ℂ f U := by
    intro w hw
    exact analyticOnNhd_regularizedTwoScaleCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl Y0 Y1 w (hsigma.trans_le hw.1.1)
  have horder : analyticOrderAt f z ≠ ⊤ :=
    analyticOrderAt_regularizedTwoScaleCarlsonZeroDetector_ne_top
      hY0 hY01 (hsigma.trans_le hz.1.1)
  have hcast := Nat.cast_analyticOrderNatAt horder
  have hdivisor : D z = (analyticOrderNatAt f z : ℤ) := by
    rw [MeromorphicOn.divisor_apply hf.meromorphicOn hz, (hf z hz).meromorphicOrderAt_eq]
    rw [← hcast]
    simp
  change z ∈ (D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha a b)).toFinset ↔
    f z = 0
  rw [(D.finiteSupport (isCompact_carlsonDetectorRectangle sigma alpha a b)).mem_toFinset]
  simp only [Function.mem_support]
  rw [hdivisor, Int.ofNat_ne_zero]
  constructor
  · intro hnat
    apply (hf z hz).analyticOrderAt_ne_zero.mp
    intro hzero
    have hzNat : (analyticOrderNatAt f z : ℕ∞) = 0 := hcast.trans hzero
    exact hnat (by simpa using hzNat)
  · intro hzero hnatZero
    have horderZero : analyticOrderAt f z = 0 := by
      rw [← hcast, hnatZero]
      rfl
    exact ((hf z hz).analyticOrderAt_eq_zero.mp horderZero) hzero

/-- A nonempty real window contains a zero-free vertical segment over any
prescribed compact height interval. -/
theorem exists_regularizedTwoScaleCarlson_vertical_ne_zero
    {Y0 Y1 : ℕ} (hY0 : 2 ≤ Y0) (hY01 : Y0 < Y1)
    {sigma0 sigma1 a b : ℝ} (hsigma0 : 0 < sigma0) (hsigma : sigma0 < sigma1) :
    ∃ x ∈ Ioo sigma0 sigma1, ∀ t ∈ Icc a b,
      regularizedTwoScaleCarlsonZeroDetector Y0 Y1 ((x : ℂ) + I * (t : ℂ)) ≠ 0 := by
  classical
  let P := regularizedTwoScaleCarlsonRectangleDivisorSupport Y0 Y1 sigma0 sigma1 a b
  let bad := P.image Complex.re
  obtain ⟨x, hx, hxbad⟩ := (Ioo_infinite hsigma).exists_notMem_finset bad
  refine ⟨x, hx, ?_⟩
  intro t ht hzero
  let z : ℂ := (x : ℂ) + I * (t : ℂ)
  have hz : z ∈ carlsonDetectorRectangle sigma0 sigma1 a b := by
    change z.re ∈ Icc sigma0 sigma1 ∧ z.im ∈ Icc a b
    constructor
    · simpa only [z, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero,
        sub_self, add_zero] using ⟨hx.1.le, hx.2.le⟩
    · simpa [z] using ht
  have hzP : z ∈ P :=
    (mem_regularizedTwoScaleCarlsonRectangleDivisorSupport_iff_zero
      hY0 hY01 hsigma0 hz).mpr hzero
  apply hxbad
  exact Finset.mem_image.mpr ⟨z, hzP, by simp [z]⟩

end PrimeNumberTheorem.CarlsonZeroDensity
