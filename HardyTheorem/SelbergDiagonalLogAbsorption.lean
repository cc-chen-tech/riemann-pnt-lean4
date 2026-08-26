import HardyTheorem.SelbergDiagonalAssembled

namespace HardyTheorem

/-! # Elementary logarithmic absorption for the diagonal remainder. -/

theorem log_two_add_fourth_div_le_rpow
    {delta Y r : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hY : 1 ≤ Y) (hr : 0 < r) :
    Real.log (2 + Y ^ 4 / delta) ≤
      (3 ^ r * Y ^ (4 * r) * delta ^ (-r)) / r := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hY4 : 1 ≤ Y ^ (4 : ℕ) := by nlinarith [sq_nonneg (Y ^ 2 - 1)]
  have hratio1 : 1 ≤ Y ^ 4 / delta := by
    rw [le_div_iff₀ hdelta]
    simpa only [one_mul] using hdelta1.trans hY4
  have harg : 2 + Y ^ 4 / delta ≤ 3 * (Y ^ 4 / delta) := by
    linarith
  have harg0 : 0 ≤ 2 + Y ^ 4 / delta := by positivity
  have hmajor0 : 0 ≤ 3 * (Y ^ 4 / delta) := by positivity
  calc
    Real.log (2 + Y ^ 4 / delta) ≤
        (2 + Y ^ 4 / delta) ^ r / r :=
      Real.log_le_rpow_div harg0 hr
    _ ≤ (3 * (Y ^ 4 / delta)) ^ r / r := by
      gcongr
    _ = (3 ^ r * Y ^ (4 * r) * delta ^ (-r)) / r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3)
        (div_nonneg (by positivity) hdelta.le)]
      rw [Real.div_rpow (by positivity) hdelta.le]
      rw [← Real.rpow_natCast Y 4, ← Real.rpow_mul hY0.le]
      rw [Real.rpow_neg hdelta.le]
      ring

theorem selbergDiagonalRemainderAbsorptionScale_le_of_power_gates
    {delta x theta Y a r : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hY : 1 ≤ Y) (hx0 : 0 ≤ x) (hxY : x ≤ Y ^ a)
    (htheta0 : 0 ≤ theta) (hthetaHalf : theta ≤ 1 / 2)
    (hr : 0 < r)
    (hpower1 : delta ^ (1 / 2 : ℝ) * Y ^ (a + 4 + r) ≤ 1)
    (hpower2 : delta ^ ((1 / 2 : ℝ) - r) *
      Y ^ (a + 4 + 5 * r) ≤ 1) :
    selbergDiagonalRemainderAbsorptionScale delta x theta Y ≤
      3 / r + 3 ^ r / (2 * r ^ 2) := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hlogY0 : 0 ≤ Real.log Y := Real.log_nonneg hY
  have hlogY := Real.log_le_rpow_div hY0.le hr
  have hlogZ := log_two_add_fourth_div_le_rpow
    hdelta hdelta1 hY hr
  have hlogZ0 : 0 ≤ Real.log (2 + Y ^ 4 / delta) := by
    apply Real.log_nonneg
    have : 0 ≤ Y ^ 4 / delta := by positivity
    linarith
  have hdhalf0 : 0 ≤ delta ^ (1 / 2 : ℝ) :=
    Real.rpow_nonneg hdelta.le _
  have hYa0 : 0 ≤ Y ^ a := Real.rpow_nonneg hY0.le _
  have hY1 : Y ^ (4 : ℝ) * Y ^ a * Y ^ r =
      Y ^ (a + 4 + r) := by
    rw [← Real.rpow_add hY0, ← Real.rpow_add hY0]
    congr 1
    ring
  have hY2 : Y ^ (4 : ℝ) * Y ^ a * Y ^ r * Y ^ (r * 4) =
      Y ^ (a + 4 + 5 * r) := by
    rw [← Real.rpow_add hY0, ← Real.rpow_add hY0,
      ← Real.rpow_add hY0]
    congr 1
    ring
  have hd : delta ^ (1 / 2 : ℝ) * delta ^ (-r) =
      delta ^ ((1 / 2 : ℝ) - r) := by
    rw [← Real.rpow_add hdelta]
    congr 1
  unfold selbergDiagonalRemainderAbsorptionScale
  calc
    delta ^ (1 / 2 : ℝ) * Y ^ 4 * x * Real.log Y *
        (3 + theta * Real.log (2 + Y ^ 4 / delta)) ≤
      delta ^ (1 / 2 : ℝ) * Y ^ 4 * Y ^ a * (Y ^ r / r) *
        (3 + (1 / 2 : ℝ) *
          ((3 ^ r * Y ^ (4 * r) * delta ^ (-r)) / r)) := by
      gcongr
    _ = (3 / r) *
          (delta ^ (1 / 2 : ℝ) * Y ^ (a + 4 + r)) +
        (3 ^ r / (2 * r ^ 2)) *
          (delta ^ ((1 / 2 : ℝ) - r) *
            Y ^ (a + 4 + 5 * r)) := by
      rw [show Y ^ (4 : ℕ) = Y ^ (4 : ℝ) by
        exact (Real.rpow_natCast Y 4).symm]
      field_simp [hr.ne']
      ring_nf
      have hterm1 :
          delta ^ (1 / 2 : ℝ) * Y ^ (4 : ℝ) * Y ^ a * Y ^ r * r * 6 =
            delta ^ (1 / 2 : ℝ) * r * Y ^ (4 + r + a) * 6 := by
        calc
          delta ^ (1 / 2 : ℝ) * Y ^ (4 : ℝ) * Y ^ a * Y ^ r * r * 6 =
              delta ^ (1 / 2 : ℝ) * r * 6 *
                (Y ^ (4 : ℝ) * Y ^ a * Y ^ r) := by ring
          _ = delta ^ (1 / 2 : ℝ) * r * Y ^ (4 + r + a) * 6 := by
            rw [hY1]
            have hexp : a + 4 + r = 4 + r + a := by ring
            rw [hexp]
            ring
      have hterm2 :
          delta ^ (1 / 2 : ℝ) * Y ^ (4 : ℝ) * Y ^ a * Y ^ r *
              3 ^ r * Y ^ (r * 4) * delta ^ (-r) =
            3 ^ r * delta ^ ((1 / 2 : ℝ) - r) *
              Y ^ (4 + r * 5 + a) := by
        calc
          delta ^ (1 / 2 : ℝ) * Y ^ (4 : ℝ) * Y ^ a * Y ^ r *
              3 ^ r * Y ^ (r * 4) * delta ^ (-r) =
            3 ^ r * (delta ^ (1 / 2 : ℝ) * delta ^ (-r)) *
              (Y ^ (4 : ℝ) * Y ^ a * Y ^ r * Y ^ (r * 4)) := by ring
          _ = 3 ^ r * delta ^ ((1 / 2 : ℝ) - r) *
              Y ^ (4 + r * 5 + a) := by
            rw [hd, hY2]
            congr 1
            ring
      rw [hterm1, hterm2]
    _ ≤ (3 / r) * 1 + (3 ^ r / (2 * r ^ 2)) * 1 := by
      gcongr
    _ = 3 / r + 3 ^ r / (2 * r ^ 2) := by ring

theorem selbergDiagonalRemainderPowerGates_of_parameters
    {delta Y a c r : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hY : 1 ≤ Y) (ha : 0 ≤ a) (hc : 0 ≤ c) (hr : 0 < r)
    (hYpow : Y ≤ delta ^ (-c))
    (hac : (a + 2) * c ≤ 1 / 4)
    (hrgap : r * (1 + 5 * c) ≤ 1 / 4 - 2 * c) :
    delta ^ (1 / 2 : ℝ) * Y ^ (a + 4 + r) ≤ 1 ∧
      delta ^ ((1 / 2 : ℝ) - r) * Y ^ (a + 4 + 5 * r) ≤ 1 := by
  have hY0 : 0 < Y := zero_lt_one.trans_le hY
  have hgap0 : 0 ≤ 1 / 4 - 2 * c := by
    have hleft0 : 0 ≤ r * (1 + 5 * c) := by positivity
    exact hleft0.trans hrgap
  have hrle : r ≤ 1 / 4 - 2 * c := by
    have hone : 1 ≤ 1 + 5 * c := by linarith
    calc
      r ≤ r * (1 + 5 * c) := by nlinarith
      _ ≤ 1 / 4 - 2 * c := hrgap
  have hb1 : 0 ≤ a + 4 + r := by linarith
  have hb2 : 0 ≤ a + 4 + 5 * r := by linarith
  have hexp1 : 0 ≤ (1 / 2 : ℝ) - c * (a + 4 + r) := by
    nlinarith
  have hexp2 : 0 ≤ (1 / 2 : ℝ) - r - c * (a + 4 + 5 * r) := by
    nlinarith
  constructor
  · have hpow := Real.rpow_le_rpow hY0.le hYpow hb1
    calc
      delta ^ (1 / 2 : ℝ) * Y ^ (a + 4 + r) ≤
          delta ^ (1 / 2 : ℝ) * (delta ^ (-c)) ^ (a + 4 + r) := by
        gcongr
      _ = delta ^ ((1 / 2 : ℝ) - c * (a + 4 + r)) := by
        rw [← Real.rpow_mul hdelta.le, ← Real.rpow_add hdelta]
        congr 1
        ring
      _ ≤ 1 := Real.rpow_le_one hdelta.le hdelta1 hexp1
  · have hpow := Real.rpow_le_rpow hY0.le hYpow hb2
    calc
      delta ^ ((1 / 2 : ℝ) - r) * Y ^ (a + 4 + 5 * r) ≤
          delta ^ ((1 / 2 : ℝ) - r) *
            (delta ^ (-c)) ^ (a + 4 + 5 * r) := by
        gcongr
      _ = delta ^ ((1 / 2 : ℝ) - r - c * (a + 4 + 5 * r)) := by
        rw [← Real.rpow_mul hdelta.le, ← Real.rpow_add hdelta]
        congr 1
        ring
      _ ≤ 1 := Real.rpow_le_one hdelta.le hdelta1 hexp2

theorem selbergDiagonalRemainderAbsorptionScale_le_of_parameters
    {delta x theta Y a c r : ℝ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hY : 1 ≤ Y) (hx0 : 0 ≤ x) (hxY : x ≤ Y ^ a)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hr : 0 < r)
    (htheta0 : 0 ≤ theta) (hthetaHalf : theta ≤ 1 / 2)
    (hYpow : Y ≤ delta ^ (-c))
    (hac : (a + 2) * c ≤ 1 / 4)
    (hrgap : r * (1 + 5 * c) ≤ 1 / 4 - 2 * c) :
    selbergDiagonalRemainderAbsorptionScale delta x theta Y ≤
      3 / r + 3 ^ r / (2 * r ^ 2) := by
  rcases selbergDiagonalRemainderPowerGates_of_parameters
    hdelta hdelta1 hY ha hc hr hYpow hac hrgap with ⟨hpower1, hpower2⟩
  exact selbergDiagonalRemainderAbsorptionScale_le_of_power_gates
    hdelta hdelta1 hY hx0 hxY htheta0 hthetaHalf hr hpower1 hpower2

theorem exists_selbergDiagonalAbsorptionExponent
    {c : ℝ} (hc : 0 ≤ c) (hcEight : c < 1 / 8) :
    ∃ r : ℝ, 0 < r ∧
      r * (1 + 5 * c) ≤ 1 / 4 - 2 * c := by
  let gap : ℝ := 1 / 4 - 2 * c
  let d : ℝ := 1 + 5 * c
  have hgap : 0 < gap := by dsimp [gap]; linarith
  have hd : 0 < d := by dsimp [d]; linarith
  refine ⟨gap / (2 * d), by positivity, ?_⟩
  dsimp [gap, d]
  field_simp [hd.ne']
  nlinarith

theorem exists_uniform_selbergDiagonalRemainderAbsorptionScale_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (hac : (a + 2) * c ≤ 1 / 4) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ {delta x theta Y : ℝ},
        0 < delta → delta ≤ 1 → 1 ≤ Y → 0 ≤ x → x ≤ Y ^ a →
        0 ≤ theta → theta ≤ 1 / 2 → Y ≤ delta ^ (-c) →
        selbergDiagonalRemainderAbsorptionScale delta x theta Y ≤ K := by
  rcases exists_selbergDiagonalAbsorptionExponent hc hcEight with
    ⟨r, hr, hrgap⟩
  let K : ℝ := 3 / r + 3 ^ r / (2 * r ^ 2)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  refine ⟨K, hK, ?_⟩
  intro delta x theta Y hdelta hdelta1 hY hx0 hxY htheta0
    hthetaHalf hYpow
  exact selbergDiagonalRemainderAbsorptionScale_le_of_parameters
    hdelta hdelta1 hY hx0 hxY ha hc hr htheta0 hthetaHalf
      hYpow hac hrgap

end HardyTheorem
