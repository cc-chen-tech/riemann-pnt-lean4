import HardyTheorem.SelbergS12Gronwall
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: high-height transfer to the one-line

This packages the short horizontal segment argument.  The segment length is
`a / log |t|`; hence the available `O(log² |t|)` logarithmic-derivative bound
costs only `exp (C a log |t|)`.
-/

theorem exists_norm_inv_riemannZeta_oneLine_le_gronwall :
    ∃ C T : ℝ, 0 ≤ C ∧ 2 ≤ T ∧
      ∀ a t : ℝ, 0 < a → a ≤ Real.log |t| → T ≤ |t| →
        ‖(riemannZeta ((1 : ℂ) + I * t))⁻¹‖ ≤
          (1 + Real.log |t| / a) *
            Real.exp (C * (Real.log |t|) ^ 2 *
              (a / Real.log |t|)) := by
  rcases
      ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
    with ⟨c, C, T, hc, hC, hT, hstrip⟩
  refine ⟨C, T, hC, hT, ?_⟩
  intro a t ha haL ht
  let L : ℝ := Real.log |t|
  let ℓ : ℝ := a / L
  let σ : ℝ := 1 + ℓ
  have ht2 : 2 ≤ |t| := hT.trans ht
  have ht1 : 1 < |t| := lt_of_lt_of_le (by norm_num) ht2
  have ht0 : t ≠ 0 := by
    intro hzero
    subst t
    norm_num at ht2
  have hL : 0 < L := by
    dsimp [L]
    exact Real.log_pos ht1
  have hℓ : 0 ≤ ℓ := by
    dsimp [ℓ]
    exact (div_pos ha hL).le
  have hℓ_one : ℓ ≤ 1 := by
    dsimp [ℓ, L]
    exact (div_le_one hL).mpr haL
  have hsafe : ∀ x ∈ Icc (0 : ℝ) ℓ,
      selbergS12HorizontalPoint σ t x ≠ 1 ∧
        riemannZeta (selbergS12HorizontalPoint σ t x) ≠ 0 := by
    intro x hx
    have hσx_lower : 1 ≤ σ - x := by
      dsimp [σ]
      linarith [hx.2]
    have hσx_upper : σ - x ≤ 2 := by
      dsimp [σ]
      linarith [hx.1, hℓ_one]
    have hcdiv : 0 ≤ c / (2 * L) := by positivity
    have hinner : 1 - c / (2 * Real.log |t|) ≤ σ - x := by
      change 1 - c / (2 * L) ≤ σ - x
      linarith
    have hz := hstrip (σ - x) t ht hinner hσx_upper
    constructor
    · intro heq
      have him := congrArg Complex.im heq
      simp only [selbergS12HorizontalPoint_im, one_im] at him
      exact ht0 him
    · simpa [selbergS12HorizontalPoint] using hz.1
  have hlog : ∀ x ∈ Icc (0 : ℝ) ℓ,
      ‖logDeriv riemannZeta (selbergS12HorizontalPoint σ t x)‖ ≤
        C * L ^ 2 := by
    intro x hx
    have hσx_lower : 1 ≤ σ - x := by
      dsimp [σ]
      linarith [hx.2]
    have hσx_upper : σ - x ≤ 2 := by
      dsimp [σ]
      linarith [hx.1, hℓ_one]
    have hcdiv : 0 ≤ c / (2 * L) := by positivity
    have hinner : 1 - c / (2 * Real.log |t|) ≤ σ - x := by
      change 1 - c / (2 * L) ≤ σ - x
      linarith
    have hz := hstrip (σ - x) t ht hinner hσx_upper
    simpa [L, selbergS12HorizontalPoint] using hz.2
  have hbase : ‖selbergS12ReciprocalAlong σ t 0‖ ≤ 1 + L / a := by
    have hb := norm_inv_riemannZeta_selbergS12MovingRightPoint_le ha ht1
    simpa [selbergS12ReciprocalAlong, selbergS12HorizontalPoint,
      selbergS12MovingRightPoint, σ, ℓ, L] using hb
  have hg := norm_selbergS12ReciprocalAlong_le_mul_exp
    hℓ hsafe hlog hbase
  simpa [selbergS12ReciprocalAlong, selbergS12HorizontalPoint, σ, ℓ, L]
    using hg

end HardyTheorem
