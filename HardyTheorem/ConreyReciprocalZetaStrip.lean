import HardyTheorem.SelbergS12Gronwall
import ZeroFreeRegion.PhragmenLindelofZeta

/-!
# An actual reciprocal-zeta bound left of the one-line

The native inner zero-free-region logarithmic-derivative bound and
horizontal Grönwall imply a uniform `|t|^(1/4) * (1 + log |t| / c)`
bound on a narrow strip crossing `Re(s) = 1`. Nonvanishing and the norm
estimate are conclusions, not assumptions. Both signs of the height
and both strip endpoints are included.

This is an analytic input for the inner Möbius Perron integral, not a
proof of that integral's full asymptotic or of the long mean-square.
See `docs/research/2026-08-30-conrey-inner-mobius-contour-proof.md`.
-/

open Complex Set

namespace HardyTheorem

/-- An actual left-strip reciprocal bound with explicit logarithmic
prefactor. No inner Möbius or long-moment estimate is assumed. -/
theorem exists_conrey_reciprocal_zeta_quarterPower_strip :
    ∃ c T : ℝ, 0 < c ∧ c ≤ 1 ∧ 2 ≤ T ∧
      ∀ σ t : ℝ, T ≤ |t| → 1 - c / Real.log |t| ≤ σ → σ ≤ 2 →
        riemannZeta ((σ : ℂ) + I * t) ≠ 0 ∧
          ‖(riemannZeta ((σ : ℂ) + I * t))⁻¹‖ ≤
            (1 + Real.log |t| / c) * Real.exp (Real.log |t| / 4) := by
  rcases ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
    with ⟨c₀, C, T₀, hc₀, hC, hT₀, hstrip⟩
  let c : ℝ := min (c₀ / 2) (1 / (8 * (C + 1)))
  have hc : 0 < c := by dsimp [c]; positivity
  have hcsmall : c ≤ 1 / (8 * (C + 1)) := min_le_right _ _
  have hcle : c ≤ c₀ / 2 := min_le_left _ _
  have hprod : c * (8 * (C + 1)) ≤ 1 :=
    (le_div_iff₀ (by positivity : 0 < 8 * (C + 1))).mp hcsmall
  have hc1 : c ≤ 1 := by nlinarith [mul_nonneg hc.le hC]
  have hCc : 2 * C * c ≤ (1 / 4 : ℝ) := by nlinarith
  let T : ℝ := max T₀ (Real.exp c)
  refine ⟨c, T, hc, hc1, hT₀.trans (le_max_left _ _), ?_⟩
  intro σ t ht hσ hσ2
  let L : ℝ := Real.log |t|
  have ht₀ : T₀ ≤ |t| := (le_max_left _ _).trans ht
  have ht2 : 2 ≤ |t| := hT₀.trans ht₀
  have ht1 : 1 < |t| := lt_of_lt_of_le one_lt_two ht2
  have hL : 0 < L := Real.log_pos ht1
  have hcL : c ≤ L := by
    have h := Real.log_le_log (Real.exp_pos c) ((le_max_right _ _).trans ht)
    simpa [L] using h
  have htne : t ≠ 0 := by
    intro hzero
    subst t
    norm_num at ht2
  have hcd : c / L ≤ c₀ / (2 * L) := by
    calc
      c / L ≤ (c₀ / 2) / L := div_le_div_of_nonneg_right hcle hL.le
      _ = c₀ / (2 * L) := by ring
  have hσinner : 1 - c₀ / (2 * Real.log |t|) ≤ σ := by
    change 1 - c₀ / (2 * L) ≤ σ
    change 1 - c / L ≤ σ at hσ
    linarith
  refine ⟨(hstrip σ t ht₀ hσinner hσ2).1, ?_⟩
  change ‖(riemannZeta ((σ : ℂ) + I * t))⁻¹‖ ≤
    (1 + L / c) * Real.exp (L / 4)
  have hbasepos : 0 ≤ 1 + L / c := by positivity
  by_cases hright : 1 + c / L ≤ σ
  · have hσ1 : 1 < σ := by linarith [div_pos hc hL]
    have hnorm := norm_inv_riemannZeta_le_re_div_sub_one
      (s := (σ : ℂ) + I * t) (by simpa using hσ1)
    have hfrac : σ / (σ - 1) ≤ 1 + L / c := by
      have hinv : (σ - 1)⁻¹ ≤ (c / L)⁻¹ :=
        (inv_le_inv₀ (by linarith : 0 < σ - 1) (div_pos hc hL)).mpr (by linarith)
      calc
        σ / (σ - 1) = 1 + (σ - 1)⁻¹ := by
          field_simp [ne_of_gt (sub_pos.mpr hσ1)]
          ring
        _ ≤ 1 + (c / L)⁻¹ := add_le_add le_rfl hinv
        _ = 1 + L / c := by rw [inv_div]
    calc
      _ ≤ σ / (σ - 1) := by simpa using hnorm
      _ ≤ 1 + L / c := hfrac
      _ ≤ (1 + L / c) * Real.exp (L / 4) :=
        le_mul_of_one_le_right hbasepos (Real.one_le_exp_iff.mpr (by positivity))
  · let σ₀ : ℝ := 1 + c / L
    let ℓ : ℝ := σ₀ - σ
    have hℓ : 0 ≤ ℓ := by dsimp [ℓ, σ₀]; linarith
    have hℓupper : ℓ ≤ 2 * c / L := by
      dsimp [ℓ, σ₀]
      change 1 - c / L ≤ σ at hσ
      rw [mul_div_assoc]
      linarith
    have hσ₀2 : σ₀ ≤ 2 := by
      have := (div_le_one hL).mpr hcL
      dsimp [σ₀]
      linarith
    have hpath : ∀ x ∈ Icc (0 : ℝ) ℓ,
        1 - c₀ / (2 * Real.log |t|) ≤ σ₀ - x ∧ σ₀ - x ≤ 2 := by
      intro x hx
      have hxupper : x ≤ σ₀ - σ := hx.2
      have hlower : σ ≤ σ₀ - x := by linarith
      exact ⟨hσinner.trans hlower, (sub_le_self _ hx.1).trans hσ₀2⟩
    have hsafe : ∀ x ∈ Icc (0 : ℝ) ℓ,
        selbergS12HorizontalPoint σ₀ t x ≠ 1 ∧
          riemannZeta (selbergS12HorizontalPoint σ₀ t x) ≠ 0 := by
      intro x hx
      constructor
      · intro heq
        have him := congrArg Complex.im heq
        simp only [selbergS12HorizontalPoint_im, one_im] at him
        exact htne him
      · simpa [selbergS12HorizontalPoint] using
          (hstrip (σ₀ - x) t ht₀ (hpath x hx).1 (hpath x hx).2).1
    have hlog : ∀ x ∈ Icc (0 : ℝ) ℓ,
        ‖logDeriv riemannZeta (selbergS12HorizontalPoint σ₀ t x)‖ ≤ C * L ^ 2 := by
      intro x hx
      simpa [selbergS12HorizontalPoint, L] using
        (hstrip (σ₀ - x) t ht₀ (hpath x hx).1 (hpath x hx).2).2
    have hbase : ‖selbergS12ReciprocalAlong σ₀ t 0‖ ≤ 1 + L / c := by
      simpa [selbergS12ReciprocalAlong, selbergS12HorizontalPoint,
        selbergS12MovingRightPoint, σ₀, L] using
        norm_inv_riemannZeta_selbergS12MovingRightPoint_le hc ht1
    have hraw := norm_selbergS12ReciprocalAlong_le_mul_exp hℓ hsafe hlog hbase
    have hexponent : C * L ^ 2 * ℓ ≤ L / 4 := by
      calc
        _ ≤ C * L ^ 2 * (2 * c / L) :=
          mul_le_mul_of_nonneg_left hℓupper (by positivity)
        _ = (2 * C * c) * L := by field_simp [hL.ne']
        _ ≤ (1 / 4 : ℝ) * L := mul_le_mul_of_nonneg_right hCc hL.le
        _ = L / 4 := by ring
    have hend : σ₀ - ℓ = σ := by dsimp [ℓ]; ring
    calc
      _ ≤ (1 + L / c) * Real.exp (C * L ^ 2 * ℓ) := by
        simpa only [selbergS12ReciprocalAlong, selbergS12HorizontalPoint, hend] using hraw
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexponent) hbasepos

end HardyTheorem
