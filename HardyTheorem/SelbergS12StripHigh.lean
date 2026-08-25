import HardyTheorem.SelbergS12StripBounded
import HardyTheorem.SelbergS12HighTransfer

open Complex Set

namespace HardyTheorem

/-!
# Selberg S12: a uniform high-height reciprocal bound on `1 ≤ re s ≤ 2`

The moving right point `1 + a / log |t|` splits the strip.  Points to its right are handled by
absolute convergence.  Points between it and the one-line are reached by the same short
Grönwall segment used for the boundary estimate.  Choosing `a` with slack makes the resulting
bound linear in `|t|`, uniformly across the strip.
-/

theorem exists_norm_inv_riemannZeta_strip_le_mul_abs_high :
    ∃ A T : ℝ, 0 ≤ A ∧ 2 ≤ T ∧
      ∀ epsilon t : ℝ, 0 ≤ epsilon → epsilon ≤ 1 → T ≤ |t| →
        ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤ A * |t| := by
  rcases
      ZeroFreeRegion.exists_riemannZeta_ne_zero_and_norm_logDeriv_le_log_sq_on_inner_zeroFreeRegion
    with ⟨c, C, T, hc, hC, hT, hstrip⟩
  let a : ℝ := 1 / (4 * (C + 1))
  let A : ℝ := 1 + 4 / a
  let T' : ℝ := max T (Real.exp a)
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hT' : 2 ≤ T' := hT.trans (le_max_left _ _)
  refine ⟨A, T', hA, hT', ?_⟩
  intro epsilon t heps0 heps1 ht
  let x : ℝ := |t|
  let L : ℝ := Real.log x
  let ell : ℝ := a / L
  let sigma : ℝ := 1 + ell
  let q : ℝ := x ^ (1 / 4 : ℝ)
  have hTx : T ≤ x := (le_max_left T (Real.exp a)).trans ht
  have hexpa : Real.exp a ≤ x := (le_max_right T (Real.exp a)).trans ht
  have hx2 : 2 ≤ x := hT.trans hTx
  have hx1 : 1 ≤ x := (by norm_num : (1 : ℝ) ≤ 2).trans hx2
  have hxpos : 0 < x := lt_of_lt_of_le zero_lt_one hx1
  have ht0 : t ≠ 0 := by
    intro hzero
    subst t
    norm_num at hx2
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (lt_of_lt_of_le one_lt_two hx2)
  have haL : a ≤ L := by
    have h := Real.log_le_log (Real.exp_pos a) hexpa
    simpa [L] using h
  have hell0 : 0 ≤ ell := (div_pos ha hLpos).le
  have hell1 : ell ≤ 1 := by
    dsimp [ell]
    exact (div_le_one hLpos).2 haL
  have hraw :
      ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤
        (1 + L / a) * Real.exp (C * L ^ 2 * (a / L)) := by
    by_cases hright : ell ≤ epsilon
    · have hre : 1 < (selbergS12StripPoint epsilon t).re := by
        simp only [selbergS12StripPoint_re]
        linarith [lt_of_lt_of_le (div_pos ha hLpos) hright]
      have hdir := norm_inv_riemannZeta_le_re_div_sub_one hre
      have hepspos : 0 < epsilon := lt_of_lt_of_le (div_pos ha hLpos) hright
      have hratio :
          (selbergS12StripPoint epsilon t).re /
              ((selbergS12StripPoint epsilon t).re - 1) =
            1 + 1 / epsilon := by
        simp only [selbergS12StripPoint_re]
        field_simp [hepspos.ne']
        ring
      have hinvle : 1 / epsilon ≤ L / a := by
        apply (div_le_div_iff₀ hepspos ha).2
        dsimp [ell] at hright
        have := hright
        field_simp [hLpos.ne'] at this
        nlinarith
      have hbase :
          ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤ 1 + L / a := by
        calc
          ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤
              (selbergS12StripPoint epsilon t).re /
                ((selbergS12StripPoint epsilon t).re - 1) := hdir
          _ = 1 + 1 / epsilon := hratio
          _ ≤ 1 + L / a := add_le_add le_rfl hinvle
      exact hbase.trans (le_mul_of_one_le_right (by positivity)
        (Real.one_le_exp (mul_nonneg (mul_nonneg hC (sq_nonneg L))
          (div_nonneg ha.le hLpos.le))))
    · have hepsell : epsilon < ell := lt_of_not_ge hright
      let d : ℝ := ell - epsilon
      have hd0 : 0 ≤ d := sub_nonneg.mpr hepsell.le
      have hdell : d ≤ ell := by dsimp [d]; linarith
      have hsafe : ∀ u ∈ Icc (0 : ℝ) d,
          selbergS12HorizontalPoint sigma t u ≠ 1 ∧
            riemannZeta (selbergS12HorizontalPoint sigma t u) ≠ 0 := by
        intro u hu
        have hreLower : 1 ≤ sigma - u := by
          dsimp [sigma, d]
          linarith [hu.2, heps0]
        have hreUpper : sigma - u ≤ 2 := by
          dsimp [sigma]
          linarith [hu.1, hell1]
        have hinner : 1 - c / (2 * L) ≤ sigma - u := by
          have hcdiv : 0 ≤ c / (2 * L) := by positivity
          linarith
        have hz := hstrip (sigma - u) t hTx
          (by simpa [L, x] using hinner) hreUpper
        constructor
        · intro heq
          have him := congrArg Complex.im heq
          simp only [selbergS12HorizontalPoint_im, one_im] at him
          exact ht0 him
        · simpa [selbergS12HorizontalPoint] using hz.1
      have hlog : ∀ u ∈ Icc (0 : ℝ) d,
          ‖logDeriv riemannZeta (selbergS12HorizontalPoint sigma t u)‖ ≤
            C * L ^ 2 := by
        intro u hu
        have hreLower : 1 ≤ sigma - u := by
          dsimp [sigma, d]
          linarith [hu.2, heps0]
        have hreUpper : sigma - u ≤ 2 := by
          dsimp [sigma]
          linarith [hu.1, hell1]
        have hinner : 1 - c / (2 * L) ≤ sigma - u := by
          have hcdiv : 0 ≤ c / (2 * L) := by positivity
          linarith
        have hz := hstrip (sigma - u) t hTx
          (by simpa [L, x] using hinner) hreUpper
        simpa only [L, x, selbergS12HorizontalPoint] using hz.2
      have hbase : ‖selbergS12ReciprocalAlong sigma t 0‖ ≤ 1 + L / a := by
        have hb := norm_inv_riemannZeta_selbergS12MovingRightPoint_le ha
          (lt_of_lt_of_le one_lt_two hx2)
        simpa [selbergS12ReciprocalAlong, selbergS12HorizontalPoint,
          selbergS12MovingRightPoint, sigma, ell, L, x] using hb
      have hg := norm_selbergS12ReciprocalAlong_le_mul_exp
        hd0 hsafe hlog hbase
      have hend : selbergS12HorizontalPoint sigma t d =
          selbergS12StripPoint epsilon t := by
        apply Complex.ext <;> simp [selbergS12HorizontalPoint,
          selbergS12StripPoint, sigma, d, ell] <;> ring
      have hexpmono :
          Real.exp (C * L ^ 2 * d) ≤
            Real.exp (C * L ^ 2 * (a / L)) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonneg_left hdell (mul_nonneg hC (sq_nonneg L))
      calc
        ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ =
            ‖selbergS12ReciprocalAlong sigma t d‖ := by
          simp only [selbergS12ReciprocalAlong, hend]
        _ ≤ (1 + L / a) * Real.exp (C * L ^ 2 * d) := hg
        _ ≤ (1 + L / a) * Real.exp (C * L ^ 2 * (a / L)) :=
          mul_le_mul_of_nonneg_left hexpmono (by positivity)
  have hCa : C * a ≤ (1 / 4 : ℝ) := by
    dsimp [a]
    have hden : 0 < 4 * (C + 1) := by positivity
    rw [one_div, ← div_eq_mul_inv]
    apply (div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 4)).2
    nlinarith
  have hexponent : C * L ^ 2 * (a / L) = (C * a) * L := by
    field_simp [hLpos.ne']
  have hexp_le_q : Real.exp (C * L ^ 2 * (a / L)) ≤ q := by
    rw [hexponent]
    have hpow : (C * a) * L ≤ (1 / 4 : ℝ) * L :=
      mul_le_mul_of_nonneg_right hCa hLpos.le
    calc
      Real.exp ((C * a) * L) ≤ Real.exp ((1 / 4 : ℝ) * L) :=
        Real.exp_le_exp.mpr hpow
      _ = q := by
        dsimp [q]
        rw [Real.rpow_def_of_pos hxpos]
        congr 1
        dsimp [L]
        ring
  have hq_nonneg : 0 ≤ q := (Real.rpow_pos_of_pos hxpos _).le
  have hq_one : 1 ≤ q := Real.one_le_rpow hx1 (by norm_num)
  have hlog_q : L ≤ 4 * q := by
    have h := Real.log_le_rpow_div hxpos.le (by norm_num : 0 < (1 / 4 : ℝ))
    change L ≤ 4 * q
    simpa [L, q, mul_comm] using h
  have hbase : 1 + L / a ≤ A * q := by
    have hdiv : L / a ≤ (4 * q) / a :=
      div_le_div_of_nonneg_right hlog_q ha.le
    have hfoura : 0 ≤ 4 / a := by positivity
    dsimp [A]
    calc
      1 + L / a ≤ 1 + (4 * q) / a := add_le_add le_rfl hdiv
      _ = 1 + (4 / a) * q := by ring
      _ ≤ q + (4 / a) * q := add_le_add hq_one le_rfl
      _ = (1 + 4 / a) * q := by ring
  have hqq : q * q = x ^ (1 / 2 : ℝ) := by
    dsimp [q]
    rw [← Real.rpow_add hxpos]
    norm_num
  have hsqrt_le : x ^ (1 / 2 : ℝ) ≤ x :=
    Real.rpow_le_self_of_one_le hx1 (by norm_num)
  calc
    ‖(riemannZeta (selbergS12StripPoint epsilon t))⁻¹‖ ≤
        (1 + L / a) * Real.exp (C * L ^ 2 * (a / L)) := hraw
    _ ≤ (A * q) * q :=
      mul_le_mul hbase hexp_le_q (Real.exp_pos _).le (mul_nonneg hA hq_nonneg)
    _ = A * (q * q) := by ring
    _ = A * x ^ (1 / 2 : ℝ) := by rw [hqq]
    _ ≤ A * x := mul_le_mul_of_nonneg_left hsqrt_le hA
    _ = A * |t| := by rfl

end HardyTheorem
