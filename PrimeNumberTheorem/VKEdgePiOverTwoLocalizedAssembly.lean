import PrimeNumberTheorem.VKEdgePiOverTwoFinitePoleFilter
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean
import PrimeNumberTheorem.VKEdgePiOverTwoLocalized

open Filter Set Topology

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Values of the normalized PNT error inside the Gaussian logarithmic
window. -/
def normalizedWindowValues (rho : ℂ) (m : ℝ) : Set ℝ :=
  (fun y => |normalizedPsiError rho y|) '' gaussianLogWindow m

/-- The least upper bound of the normalized PNT error in one Gaussian
logarithmic window. -/
def normalizedWindowSup (rho : ℂ) (m : ℝ) : ℝ :=
  sSup (normalizedWindowValues rho m)

/--
The quantitative output required from the polynomial-weighted contour shift.

`signal` is the paired target residue transform, `coefficient` is the
Gaussian average of the absolute dual kernel including all polynomial-kernel
perturbations, and `remainder` contains the far-pole, contour, and tail
errors. The only inequality field is the direct estimate corresponding to
equation (32) of the localization argument; no window witness or oscillation
conclusion is assumed.
-/
structure LocalizedContourData (rho : ℂ)
    (multiplicity mean : ℝ) where
  signal : ℝ → ℝ
  coefficient : ℝ → ℝ
  remainder : ℝ → ℝ
  signal_tendsto :
    Tendsto signal atTop (𝓝 (2 * multiplicity))
  coefficient_tendsto :
    Tendsto coefficient atTop (𝓝 (2 * mean))
  remainder_tendsto :
    Tendsto remainder atTop (𝓝 0)
  eventually_coefficient_pos :
    ∀ᶠ m : ℝ in atTop, 0 < coefficient m
  eventually_window_bddAbove :
    ∀ᶠ m : ℝ in atTop, BddAbove (normalizedWindowValues rho m)
  eventually_upper_bound :
    ∀ᶠ m : ℝ in atTop,
      signal m ≤
        normalizedWindowSup rho m * coefficient m + remainder m

private theorem normalizedWindowValues_nonempty
    (rho : ℂ) {m : ℝ} (hm : 0 ≤ m) :
    (normalizedWindowValues rho m).Nonempty := by
  refine ⟨|normalizedPsiError rho (4 * m)|, ?_⟩
  exact ⟨4 * m, ⟨le_rfl, by nlinarith⟩, rfl⟩

/--
The contour signal and kernel limits force every sufficiently late
logarithmic window to contain a normalized PNT-error value below no constant
strictly smaller than `multiplicity / mean`.
-/
theorem LocalizedContourData.eventually_exists_normalizedPsiError_gt
    {rho : ℂ} {multiplicity mean C : ℝ}
    (data : LocalizedContourData rho multiplicity mean)
    (_hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ m : ℝ in atTop,
      ∃ y ∈ gaussianLogWindow m,
        C < |normalizedPsiError rho y| := by
  have hmeanTwo : (2 * mean : ℝ) ≠ 0 := by positivity
  have hratio :
      Tendsto
        (fun m =>
          (data.signal m - data.remainder m) /
            data.coefficient m)
        atTop (𝓝 (multiplicity / mean)) := by
    have h :=
      (data.signal_tendsto.sub data.remainder_tendsto).div
        data.coefficient_tendsto hmeanTwo
    convert h using 1
    · congr 1
      field_simp
      ring
  have hratioLower :
      ∀ᶠ m : ℝ in atTop,
        C <
          (data.signal m - data.remainder m) /
            data.coefficient m :=
    (tendsto_order.1 hratio).1 C hC
  filter_upwards [
      data.eventually_coefficient_pos,
      data.eventually_window_bddAbove,
      data.eventually_upper_bound,
      eventually_ge_atTop (0 : ℝ),
      hratioLower] with m hcoefficient hbdd hupper hm hClower
  have hnumerator :
      data.signal m - data.remainder m ≤
        normalizedWindowSup rho m * data.coefficient m := by
    linarith
  have hratioLe :
      (data.signal m - data.remainder m) /
          data.coefficient m ≤ normalizedWindowSup rho m :=
    (div_le_iff₀ hcoefficient).2 (by
      simpa [mul_comm] using hnumerator)
  have hCSup : C < normalizedWindowSup rho m :=
    hClower.trans_le hratioLe
  rcases
      (lt_csSup_iff hbdd (normalizedWindowValues_nonempty rho hm)).1 hCSup with
    ⟨value, ⟨y, hyWindow, rfl⟩, hyValue⟩
  exact ⟨y, hyWindow, hyValue⟩

/--
After `m = log Y / 4`, the conditional contour assembly produces a standard
Chebyshev-error witness in every sufficiently late power interval
`[Y,Y^7]`.
-/
theorem LocalizedContourData.eventually_exists_psiError_in_powerSevenWindow
    {rho : ℂ} {multiplicity mean C : ℝ}
    (data : LocalizedContourData rho multiplicity mean)
    (hrho : rho ≠ 0)
    (hmultiplicity : 0 < multiplicity) (hmean : 0 < mean)
    (hC : C < multiplicity / mean) :
    ∀ᶠ Y : ℝ in atTop,
      ∃ x ∈ powerSevenWindow Y,
        C * (x ^ rho.re / ‖rho‖) <
          |chebyshevPsi x - x| := by
  have hmAtTop :
      Tendsto (fun Y : ℝ => Real.log Y / 4) atTop atTop := by
    have h :=
      Real.tendsto_log_atTop.const_mul_atTop
        (show 0 < (1 / 4 : ℝ) by norm_num)
    simpa [div_eq_mul_inv, mul_comm] using h
  have hlocal :=
    hmAtTop.eventually
      (data.eventually_exists_normalizedPsiError_gt
        hmultiplicity hmean hC)
  filter_upwards [hlocal, eventually_ge_atTop (1 : ℝ)] with Y hYLocal hY
  rcases hYLocal with ⟨y, hyWindow, hyValue⟩
  apply
    exists_psiError_in_powerSevenWindow_of_normalizedPsiError
      hrho hY
  refine ⟨y, ?_, hyValue⟩
  rw [← gaussianLogWindow_log_div_four Y]
  exact hyWindow

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
