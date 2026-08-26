import HardyTheorem.SelbergOffDiagonalTwoSides

namespace HardyTheorem

/-! # Power absorption for Selberg's explicit off-diagonal majorant

This file only absorbs the already proved numerical majorant.  It does not
identify that majorant with the off-diagonal part of `J`; that object-level
Fubini and square-expansion bridge is kept as a separate theorem.
-/

noncomputable def selbergOffDiagonalExplicitBracket
    (delta : ℝ) (X : ℕ) : ℝ :=
  (X : ℝ) ^ 4 * (1 + Real.log (X : ℝ)) *
      selbergOffDiagonalUniformL delta X +
    (X : ℝ) ^ 2 * (1 + Real.log (X : ℝ)) ^ 2 *
      selbergOffDiagonalUniformW delta X

noncomputable def selbergOffDiagonalLogEnvelope
    (delta : ℝ) (X : ℕ) : ℝ :=
  1 + Real.log ((X : ℝ) ^ 2 / delta)

theorem selbergOffDiagonalExplicitBracket_le_five_mul
    {delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hXexp : Real.exp 1 ≤ (X : ℝ)) :
    selbergOffDiagonalExplicitBracket delta X ≤
      5 * (X : ℝ) ^ 4 * selbergOffDiagonalLogEnvelope delta X ^ 4 := by
  let Y : ℝ := X
  let z : ℝ := Y ^ 2 / delta
  let ell : ℝ := 1 + Real.log z
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num)).trans hXexp
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hz1 : 1 ≤ z := by
    dsimp [z]
    rw [one_le_div hdelta]
    have hYsq : 1 ≤ Y ^ 2 := by nlinarith
    exact hdelta1.trans hYsq
  have hz0 : 0 < z := zero_lt_one.trans_le hz1
  have hYz : Y ≤ z := by
    dsimp [z]
    rw [le_div_iff₀ hdelta]
    have hYdelta : Y * delta ≤ Y :=
      mul_le_of_le_one_right hY0.le hdelta1
    have hYY : Y ≤ Y ^ 2 := by nlinarith
    exact hYdelta.trans hYY
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hlogYz : Real.log Y ≤ Real.log z := Real.log_le_log hY0 hYz
  have hell1 : 1 ≤ ell := by dsimp [ell]; linarith
  have hell0 : 0 ≤ ell := zero_le_one.trans hell1
  have hlogYell : Real.log Y ≤ ell := hlogYz.trans (by dsimp [ell]; linarith)
  have hOneLogYell : 1 + Real.log Y ≤ ell := by
    dsimp [ell]
    linarith
  have hlogTwo : Real.log 2 ≤ (1 : ℝ) := by
    exact (Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)).trans_eq
      (by norm_num)
  have hL : selbergOffDiagonalUniformL delta X ≤ ell := by
    have harg : 2 * (X : ℝ) ^ 2 / delta = 2 * z := by
      dsimp [Y, z]
      ring
    unfold selbergOffDiagonalUniformL
    rw [harg, Real.log_mul (by norm_num) hz0.ne']
    dsimp [ell]
    linarith
  have hL0 : 0 ≤ selbergOffDiagonalUniformL delta X := by
    apply Real.log_nonneg
    rw [one_le_div hdelta]
    have hYsq : 1 ≤ Y ^ 2 := by nlinarith
    dsimp [Y] at hYsq
    nlinarith
  have hW : selbergOffDiagonalUniformW delta X ≤ 4 * ell ^ 2 := by
    unfold selbergOffDiagonalUniformW
    change (Real.log Y + Real.log z) *
        selbergOffDiagonalUniformL delta X + 2 ≤ 4 * ell ^ 2
    have hsum : Real.log Y + Real.log z ≤ 2 * ell := by
      dsimp [ell]
      linarith
    have hprod : (Real.log Y + Real.log z) *
        selbergOffDiagonalUniformL delta X ≤ 2 * ell ^ 2 := by
      calc
        (Real.log Y + Real.log z) *
            selbergOffDiagonalUniformL delta X ≤
          (2 * ell) * ell := by gcongr
        _ = 2 * ell ^ 2 := by ring
    have hellsq : 1 ≤ ell ^ 2 := by nlinarith
    linarith
  have hW0 : 0 ≤ selbergOffDiagonalUniformW delta X := by
    have hXone : 1 ≤ X := by
      have : (1 : ℝ) ≤ (X : ℝ) := by simpa only [Y] using hY1
      exact_mod_cast this
    exact selbergOffDiagonalUniformW_nonneg hdelta hdelta1
      hXone
  have hY2Y4 : Y ^ 2 ≤ Y ^ 4 := by nlinarith [sq_nonneg (Y ^ 2 - Y)]
  have hell2ell4 : ell ^ 2 ≤ ell ^ 4 := by
    nlinarith [sq_nonneg (ell ^ 2 - ell)]
  change Y ^ 4 * (1 + Real.log Y) *
        selbergOffDiagonalUniformL delta X +
      Y ^ 2 * (1 + Real.log Y) ^ 2 *
        selbergOffDiagonalUniformW delta X ≤ 5 * Y ^ 4 * ell ^ 4
  have hfirst : Y ^ 4 * (1 + Real.log Y) *
      selbergOffDiagonalUniformL delta X ≤ Y ^ 4 * ell ^ 2 := by
    calc
      Y ^ 4 * (1 + Real.log Y) *
          selbergOffDiagonalUniformL delta X ≤ Y ^ 4 * ell * ell := by
        gcongr
      _ = Y ^ 4 * ell ^ 2 := by ring
  have hsecond : Y ^ 2 * (1 + Real.log Y) ^ 2 *
      selbergOffDiagonalUniformW delta X ≤ 4 * Y ^ 4 * ell ^ 4 := by
    calc
      Y ^ 2 * (1 + Real.log Y) ^ 2 *
          selbergOffDiagonalUniformW delta X ≤
        Y ^ 2 * ell ^ 2 * (4 * ell ^ 2) := by gcongr
      _ = 4 * Y ^ 2 * ell ^ 4 := by ring
      _ ≤ 4 * Y ^ 4 * ell ^ 4 := by gcongr
  calc
    Y ^ 4 * (1 + Real.log Y) * selbergOffDiagonalUniformL delta X +
        Y ^ 2 * (1 + Real.log Y) ^ 2 *
          selbergOffDiagonalUniformW delta X ≤
      Y ^ 4 * ell ^ 2 + 4 * Y ^ 4 * ell ^ 4 := add_le_add hfirst hsecond
    _ ≤ Y ^ 4 * ell ^ 4 + 4 * Y ^ 4 * ell ^ 4 := by gcongr
    _ = 5 * Y ^ 4 * ell ^ 4 := by ring

noncomputable def selbergOffDiagonalAbsorptionScale
    (delta theta : ℝ) (X : ℕ) : ℝ :=
  8 * theta * delta ^ (1 / 2 : ℝ) * Real.log (X : ℝ) *
    selbergOffDiagonalExplicitBracket delta X

theorem selbergOffDiagonalAbsorptionScale_le_power
    {delta theta r : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    {X : ℕ} (hXexp : Real.exp 1 ≤ (X : ℝ))
    (htheta0 : 0 ≤ theta) (hthetaHalf : theta ≤ 1 / 2)
    (hr : 0 < r) :
    selbergOffDiagonalAbsorptionScale delta theta X ≤
      20 * (1 + 1 / r) ^ 5 *
        delta ^ ((1 / 2 : ℝ) - 5 * r) *
        (X : ℝ) ^ (4 + 10 * r) := by
  let Y : ℝ := X
  let z : ℝ := Y ^ 2 / delta
  let ell : ℝ := 1 + Real.log z
  have hY1 : 1 ≤ Y := (Real.one_le_exp (by norm_num)).trans hXexp
  have hY0 : 0 < Y := zero_lt_one.trans_le hY1
  have hz1 : 1 ≤ z := by
    dsimp [z]
    rw [one_le_div hdelta]
    have hYsq : 1 ≤ Y ^ 2 := by nlinarith
    exact hdelta1.trans hYsq
  have hz0 : 0 < z := zero_lt_one.trans_le hz1
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY1
  have hlogz0 : 0 ≤ Real.log z := Real.log_nonneg hz1
  have hell0 : 0 ≤ ell := by dsimp [ell]; linarith
  have hlogYell : Real.log Y ≤ ell := by
    have hYz : Y ≤ z := by
      dsimp [z]
      rw [le_div_iff₀ hdelta]
      have hYdelta : Y * delta ≤ Y :=
        mul_le_of_le_one_right hY0.le hdelta1
      have hYY : Y ≤ Y ^ 2 := by nlinarith
      exact hYdelta.trans hYY
    exact (Real.log_le_log hY0 hYz).trans (by dsimp [ell]; linarith)
  have hbracket := selbergOffDiagonalExplicitBracket_le_five_mul
    hdelta hdelta1 hXexp
  have hbracket0 : 0 ≤ selbergOffDiagonalExplicitBracket delta X := by
    have hXone : 1 ≤ X := by
      have : (1 : ℝ) ≤ (X : ℝ) := by simpa only [Y] using hY1
      exact_mod_cast this
    have hL0 := selbergOffDiagonalUniformL_nonneg hdelta hdelta1 hXone
    have hW0 := selbergOffDiagonalUniformW_nonneg hdelta hdelta1 hXone
    unfold selbergOffDiagonalExplicitBracket
    positivity
  have hscaleEnvelope :
      selbergOffDiagonalAbsorptionScale delta theta X ≤
        20 * delta ^ (1 / 2 : ℝ) * Y ^ 4 * ell ^ 5 := by
    unfold selbergOffDiagonalAbsorptionScale
    change 8 * theta * delta ^ (1 / 2 : ℝ) * Real.log Y *
        selbergOffDiagonalExplicitBracket delta X ≤ _
    calc
      8 * theta * delta ^ (1 / 2 : ℝ) * Real.log Y *
          selbergOffDiagonalExplicitBracket delta X ≤
        8 * (1 / 2 : ℝ) * delta ^ (1 / 2 : ℝ) * ell *
          (5 * Y ^ 4 * ell ^ 4) := by
        have hbracket' : selbergOffDiagonalExplicitBracket delta X ≤
            5 * Y ^ 4 * ell ^ 4 := by
          simpa only [Y, ell, z, selbergOffDiagonalLogEnvelope] using hbracket
        gcongr
      _ = 20 * delta ^ (1 / 2 : ℝ) * Y ^ 4 * ell ^ 5 := by ring
  have hlogPower : Real.log z ≤ z ^ r / r :=
    Real.log_le_rpow_div hz0.le hr
  have hzpow1 : 1 ≤ z ^ r := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow one_pos.le hz1 hr.le
  have hellPower : ell ≤ (1 + 1 / r) * z ^ r := by
    dsimp [ell]
    calc
      1 + Real.log z ≤ 1 + z ^ r / r := by gcongr
      _ ≤ z ^ r + z ^ r / r := by gcongr
      _ = (1 + 1 / r) * z ^ r := by ring
  have hcoef0 : 0 ≤ 1 + 1 / r := by positivity
  have hpowEll : ell ^ 5 ≤ ((1 + 1 / r) * z ^ r) ^ 5 := by
    exact pow_le_pow_left₀ hell0 hellPower 5
  calc
    selbergOffDiagonalAbsorptionScale delta theta X ≤
        20 * delta ^ (1 / 2 : ℝ) * Y ^ 4 * ell ^ 5 := hscaleEnvelope
    _ ≤ 20 * delta ^ (1 / 2 : ℝ) * Y ^ 4 *
        ((1 + 1 / r) * z ^ r) ^ 5 := by gcongr
    _ = 20 * (1 + 1 / r) ^ 5 *
        delta ^ ((1 / 2 : ℝ) - 5 * r) * Y ^ (4 + 10 * r) := by
      have hzpow : (z ^ r) ^ (5 : ℕ) = z ^ (5 * r) := by
        rw [← Real.rpow_natCast]
        rw [← Real.rpow_mul hz0.le]
        congr 1
        ring
      have hYpow : (Y ^ 2 / delta) ^ (5 * r) =
          Y ^ (10 * r) * delta ^ (-(5 * r)) := by
        rw [Real.div_rpow (sq_nonneg Y) hdelta.le]
        rw [← Real.rpow_natCast Y 2, ← Real.rpow_mul hY0.le]
        rw [Real.rpow_neg hdelta.le]
        congr 2
        ring
      have hdeltaPow : delta ^ (1 / 2 : ℝ) * delta ^ (-(5 * r)) =
          delta ^ ((1 / 2 : ℝ) - 5 * r) := by
        rw [← Real.rpow_add hdelta]
        congr 1
      have hYPow : Y ^ (4 : ℕ) * Y ^ (10 * r) = Y ^ (4 + 10 * r) := by
        rw [← Real.rpow_natCast Y 4, ← Real.rpow_add hY0]
        congr 1
      dsimp [z]
      rw [mul_pow, hzpow, hYpow]
      calc
        20 * delta ^ (1 / 2 : ℝ) * Y ^ 4 *
            ((1 + 1 / r) ^ 5 *
              (Y ^ (10 * r) * delta ^ (-(5 * r)))) =
          20 * (1 + 1 / r) ^ 5 *
            (delta ^ (1 / 2 : ℝ) * delta ^ (-(5 * r))) *
            (Y ^ (4 : ℕ) * Y ^ (10 * r)) := by ring
        _ = 20 * (1 + 1 / r) ^ 5 *
            delta ^ ((1 / 2 : ℝ) - 5 * r) * Y ^ (4 + 10 * r) := by
          rw [hdeltaPow, hYPow]

theorem selbergOffDiagonalPowerGate_of_parameters
    {delta Y c r : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hY : 1 ≤ Y) (hc : 0 ≤ c) (hr : 0 < r)
    (hYpow : Y ≤ delta ^ (-c))
    (hrgap : r * (5 + 10 * c) ≤ 1 / 2 - 4 * c) :
    delta ^ ((1 / 2 : ℝ) - 5 * r) * Y ^ (4 + 10 * r) ≤ 1 := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hb : 0 ≤ 4 + 10 * r := by positivity
  have hexp : 0 ≤ (1 / 2 : ℝ) - 5 * r - c * (4 + 10 * r) := by
    nlinarith
  have hpow := Real.rpow_le_rpow hY0.le hYpow hb
  calc
    delta ^ ((1 / 2 : ℝ) - 5 * r) * Y ^ (4 + 10 * r) ≤
        delta ^ ((1 / 2 : ℝ) - 5 * r) *
          (delta ^ (-c)) ^ (4 + 10 * r) := by gcongr
    _ = delta ^ ((1 / 2 : ℝ) - 5 * r - c * (4 + 10 * r)) := by
      rw [← Real.rpow_mul hdelta.le, ← Real.rpow_add hdelta]
      congr 1
      ring
    _ ≤ 1 := Real.rpow_le_one hdelta.le hdelta1 hexp

theorem exists_selbergOffDiagonalAbsorptionExponent
    {c : ℝ} (hc : 0 ≤ c) (hcEight : c < 1 / 8) :
    ∃ r : ℝ, 0 < r ∧
      r * (5 + 10 * c) ≤ 1 / 2 - 4 * c := by
  let gap : ℝ := 1 / 2 - 4 * c
  let d : ℝ := 5 + 10 * c
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  refine ⟨gap / (2 * d), by positivity, ?_⟩
  dsimp [gap, d]
  field_simp [hd.ne']
  nlinarith

theorem exists_uniform_selbergOffDiagonalAbsorptionScale_le
    {c : ℝ} (hc : 0 ≤ c) (hcEight : c < 1 / 8) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {delta theta : ℝ} {X : ℕ},
        0 < delta → delta ≤ 1 → Real.exp 1 ≤ (X : ℝ) →
        0 ≤ theta → theta ≤ 1 / 2 → (X : ℝ) ≤ delta ^ (-c) →
        selbergOffDiagonalAbsorptionScale delta theta X ≤ K := by
  rcases exists_selbergOffDiagonalAbsorptionExponent hc hcEight with
    ⟨r, hr, hrgap⟩
  let K : ℝ := 20 * (1 + 1 / r) ^ 5
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro delta theta X hdelta hdelta1 hXexp htheta0 hthetaHalf hXpow
  have hY : 1 ≤ (X : ℝ) := (Real.one_le_exp (by norm_num)).trans hXexp
  have hscale := selbergOffDiagonalAbsorptionScale_le_power
    hdelta hdelta1 hXexp htheta0 hthetaHalf hr
  have hgate := selbergOffDiagonalPowerGate_of_parameters
    hdelta hdelta1 hY hc hr hXpow hrgap
  calc
    selbergOffDiagonalAbsorptionScale delta theta X ≤
        20 * (1 + 1 / r) ^ 5 *
          (delta ^ ((1 / 2 : ℝ) - 5 * r) *
            (X : ℝ) ^ (4 + 10 * r)) := by
      simpa only [mul_assoc] using hscale
    _ ≤ 20 * (1 + 1 / r) ^ 5 * 1 := by gcongr
    _ = K := by simp [K]

theorem selbergOffDiagonalOscillatoryMajorant_le_of_absorptionScale
    {delta x theta K : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hXexp : Real.exp 1 ≤ (X : ℝ))
    (hx : 1 ≤ x) (htheta : 0 < theta) (hthetaHalf : theta ≤ 1 / 2)
    (hK : 0 ≤ K)
    (hscale : selbergOffDiagonalAbsorptionScale delta theta X ≤ K) :
    selbergOffDiagonalOscillatoryMajorant delta x theta X ≤
      K * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
        (theta * Real.log (X : ℝ))) := by
  have hXone : 1 ≤ X := by
    have : 1 ≤ (X : ℝ) := (Real.one_le_exp (by norm_num)).trans hXexp
    exact_mod_cast this
  have hmajor := selbergOffDiagonalOscillatoryMajorant_le_explicit
    hdelta hdelta1 hx htheta.le hXone
  have hlog : 0 < Real.log (X : ℝ) := by
    have hlogLower : (1 : ℝ) ≤ Real.log (X : ℝ) := by
      have := Real.log_le_log (Real.exp_pos 1) hXexp
      simpa using this
    linarith
  let T : ℝ := delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
    (theta * Real.log (X : ℝ))
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hfactor :
      8 * x ^ (-theta) * selbergOffDiagonalExplicitBracket delta X =
        selbergOffDiagonalAbsorptionScale delta theta X * T := by
    unfold selbergOffDiagonalAbsorptionScale
    dsimp [T]
    have hcancel : delta ^ (1 / 2 : ℝ) *
        delta ^ (-(1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hdelta]
      norm_num
    field_simp [htheta.ne', hlog.ne']
    calc
      selbergOffDiagonalExplicitBracket delta X =
          selbergOffDiagonalExplicitBracket delta X * 1 := by ring
      _ = selbergOffDiagonalExplicitBracket delta X *
          (delta ^ (1 / 2 : ℝ) * delta ^ (-(1 / 2 : ℝ))) := by rw [hcancel]
      _ = selbergOffDiagonalExplicitBracket delta X *
          delta ^ (1 / 2 : ℝ) * delta ^ (-(1 / 2 : ℝ)) := by ring
  calc
    selbergOffDiagonalOscillatoryMajorant delta x theta X ≤
        8 * x ^ (-theta) * selbergOffDiagonalExplicitBracket delta X := by
      simpa only [selbergOffDiagonalExplicitBracket] using hmajor
    _ = selbergOffDiagonalAbsorptionScale delta theta X * T := hfactor
    _ ≤ K * T := mul_le_mul_of_nonneg_right hscale hT0
    _ = _ := rfl

theorem exists_selbergOffDiagonalOscillatoryMajorant_le
    {c : ℝ} (hc : 0 ≤ c) (hcEight : c < 1 / 8) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ (X : ℕ) (delta x theta : ℝ),
        0 < delta → delta ≤ 1 → Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-c) → 1 ≤ x →
        0 < theta → theta ≤ 1 / 2 →
        selbergOffDiagonalOscillatoryMajorant delta x theta X ≤
          K * (delta ^ (-(1 / 2 : ℝ)) * x ^ (-theta) /
            (theta * Real.log (X : ℝ))) := by
  rcases exists_uniform_selbergOffDiagonalAbsorptionScale_le hc hcEight with
    ⟨K, hK, hscale⟩
  refine ⟨K, hK, ?_⟩
  intro X delta x theta hdelta hdelta1 hXexp hXpow hx htheta hthetaHalf
  exact selbergOffDiagonalOscillatoryMajorant_le_of_absorptionScale
    hdelta hdelta1 hXexp hx htheta hthetaHalf hK
      (hscale hdelta hdelta1 hXexp htheta.le hthetaHalf hXpow)

end HardyTheorem
