import HardyTheorem.SelbergNonconstantFourierMass
import HardyTheorem.SelbergSArithmeticHarmonic

open Complex
open scoped BigOperators

namespace HardyTheorem

/-! # The elementary residue in Selberg's S1 kernel -/

private theorem abs_selbergResidueTaperedCoeff_le_one
    {X n : ℕ} (hX : 2 ≤ X) (hn1 : 1 ≤ n) (hnX : n ≤ X) :
    |selbergSqrtZetaTaperedCoeff X n| ≤ 1 := by
  have hweight := selbergMoebiusWeight_mem_Icc hX hn1 hnX
  rw [selbergSqrtZetaTaperedCoeff, abs_mul, abs_of_nonneg hweight.1]
  calc
    |selbergSqrtZetaCoeff n| * selbergMoebiusWeight X n ≤
        1 * selbergMoebiusWeight X n :=
      mul_le_mul_of_nonneg_right
        (abs_selbergSqrtZetaCoeff_le_one_light n) hweight.1
    _ ≤ 1 := by simpa using hweight.2

theorem norm_selbergSqrtZetaPsi_zero_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 0‖ ≤ (X : ℝ) := by
  unfold selbergSqrtZetaPsi selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ (0 : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ (0 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.Icc 1 X, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      simpa using abs_selbergResidueTaperedCoeff_le_one hX
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
    _ = (X : ℝ) := by
      simp [Nat.card_Icc]

theorem norm_selbergSqrtZetaPsi_one_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 1‖ ≤ 1 + Real.log (X : ℝ) := by
  unfold selbergSqrtZetaPsi selbergMollifier
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ (1 : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ (1 : ℂ))‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Icc 1 X, (n : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : 0 < n := (Finset.mem_Icc.mp hn).1
      rw [Complex.cpow_one, norm_mul, norm_div, norm_one,
        Complex.norm_natCast]
      simp only [Complex.norm_real, Real.norm_eq_abs]
      have hcoeff := abs_selbergResidueTaperedCoeff_le_one hX
        (Finset.mem_Icc.mp hn).1 (Finset.mem_Icc.mp hn).2
      have hnnonneg : 0 ≤ (n : ℝ)⁻¹ := by positivity
      simpa [one_div] using
        mul_le_mul_of_nonneg_right hcoeff hnnonneg
    _ ≤ 1 + Real.log (X : ℝ) := selberg_sum_Icc_inv_le_one_add_log X

theorem norm_selbergSqrtZetaPsi_one_mul_zero_le
    {X : ℕ} (hX : 2 ≤ X) :
    ‖selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0‖ ≤
      (X : ℝ) * (1 + Real.log (X : ℝ)) := by
  rw [norm_mul]
  calc
    ‖selbergSqrtZetaPsi X 1‖ * ‖selbergSqrtZetaPsi X 0‖ ≤
        (1 + Real.log (X : ℝ)) * (X : ℝ) :=
      mul_le_mul (norm_selbergSqrtZetaPsi_one_le hX)
        (norm_selbergSqrtZetaPsi_zero_le hX) (norm_nonneg _)
        (by positivity)
    _ = (X : ℝ) * (1 + Real.log (X : ℝ)) := mul_comm _ _

theorem normSq_selbergResidueInverseFourierKernel
    {delta : ℝ} (hdelta : 0 < delta)
    (hdeltaPi : delta < Real.pi / 2) (X : ℕ) (y : ℝ) :
    Complex.normSq (selbergResidueInverseFourierKernel delta X y) =
      (1 / 4 : ℝ) * Real.exp (-y) *
        Complex.normSq
          (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
  have hz :
      ‖selbergFourierZ delta y ^ (1 / 2 : ℂ)‖ =
        Real.exp (-y / 2) := by
    convert norm_selbergFourierZ_cpow
      hdelta hdeltaPi y (1 / 2) 0 using 1 <;> norm_num
    ring
  have hexp : Real.exp (-y / 2) ^ 2 = Real.exp (-y) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  unfold selbergResidueInverseFourierKernel
  simp only [Complex.normSq_eq_norm_sq, norm_mul, norm_div, norm_one]
  have htwo : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [htwo, hz]
  calc
    (1 / 2 * Real.exp (-y / 2) * ‖selbergSqrtZetaPsi X 1‖ *
        ‖selbergSqrtZetaPsi X 0‖) ^ 2 =
      (1 / 4 : ℝ) * Real.exp (-y / 2) ^ 2 *
        (‖selbergSqrtZetaPsi X 1‖ * ‖selbergSqrtZetaPsi X 0‖) ^ 2 := by ring
    _ = _ := by rw [hexp]

theorem normSq_selbergSqrtZetaPsi_one_mul_zero_le_fourth
    {X : ℕ} (hX : 2 ≤ X) :
    Complex.normSq
        (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) ≤
      (X : ℝ) ^ 4 := by
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hlog : 1 + Real.log (X : ℝ) ≤ (X : ℝ) := by
    nlinarith [Real.log_le_sub_one_of_pos hXpos]
  have hnorm :
      ‖selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0‖ ≤
        (X : ℝ) ^ 2 := by
    calc
      ‖selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0‖ ≤
          (X : ℝ) * (1 + Real.log (X : ℝ)) :=
        norm_selbergSqrtZetaPsi_one_mul_zero_le hX
      _ ≤ (X : ℝ) * (X : ℝ) :=
        mul_le_mul_of_nonneg_left hlog hXpos.le
      _ = (X : ℝ) ^ 2 := by ring
  rw [Complex.normSq_eq_norm_sq]
  calc
    ‖selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0‖ ^ 2 ≤
        ((X : ℝ) ^ 2) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ = (X : ℝ) ^ 4 := by ring

theorem selberg_fourth_power_le_delta_neg_half
    {c delta : ℝ} {X : ℕ}
    (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (_hc : 0 ≤ c) (hcEight : c < 1 / 8)
    (hX : 2 ≤ X) (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    (X : ℝ) ^ 4 ≤ delta ^ (-(1 / 2 : ℝ)) := by
  have hXpos : 0 < (X : ℝ) := by exact_mod_cast (show 0 < X by omega)
  have hpow :
      (X : ℝ) ^ (4 : ℝ) ≤ (delta ^ (-c)) ^ (4 : ℝ) :=
    Real.rpow_le_rpow hXpos.le hXpow (by norm_num)
  calc
    (X : ℝ) ^ 4 = (X : ℝ) ^ (4 : ℝ) := by
      exact (Real.rpow_natCast (X : ℝ) 4).symm
    _ ≤ (delta ^ (-c)) ^ (4 : ℝ) := hpow
    _ = delta ^ (-c * 4) := by rw [← Real.rpow_mul hdelta.le]
    _ ≤ delta ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_le_rpow_of_exponent_ge hdelta hdelta1
        (by linarith only [hcEight])

theorem normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half
    {c delta : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ} (hX : 2 ≤ X)
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) (y : ℝ) :
    Complex.normSq (selbergResidueInverseFourierKernel delta X y) ≤
      delta ^ (-(1 / 2 : ℝ)) * Real.exp (-y) := by
  rw [normSq_selbergResidueInverseFourierKernel hdelta hdeltaPi X y]
  have hcoeff := normSq_selbergSqrtZetaPsi_one_mul_zero_le_fourth hX
  have hpower := selberg_fourth_power_le_delta_neg_half
    hdelta hdelta1 hc hcEight hX hXpow
  have hexp0 : 0 ≤ Real.exp (-y) := (Real.exp_pos _).le
  have hnormSq0 :
      0 ≤ Complex.normSq
        (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) :=
    Complex.normSq_nonneg _
  calc
    (1 / 4 : ℝ) * Real.exp (-y) *
        Complex.normSq
          (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) ≤
      Real.exp (-y) *
        Complex.normSq
          (selbergSqrtZetaPsi X 1 * selbergSqrtZetaPsi X 0) := by
      nlinarith
    _ ≤ Real.exp (-y) * (X : ℝ) ^ 4 :=
      mul_le_mul_of_nonneg_left hcoeff hexp0
    _ ≤ Real.exp (-y) * delta ^ (-(1 / 2 : ℝ)) :=
      mul_le_mul_of_nonneg_left hpower hexp0
    _ = delta ^ (-(1 / 2 : ℝ)) * Real.exp (-y) := mul_comm _ _

theorem integral_normSq_selbergResidueInverseFourierKernel_low_le_delta_neg_half
    {c delta L : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ} (hX : 2 ≤ X)
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) :
    (∫ y in Set.Ioc 0 L,
      Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      delta ^ (-(1 / 2 : ℝ)) := by
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  have hD0 : 0 ≤ D := Real.rpow_nonneg hdelta.le _
  have hmajorInt : MeasureTheory.IntegrableOn
      (fun y : ℝ => D * Real.exp (-y)) (Set.Ioi 0) := by
    change MeasureTheory.Integrable (fun y : ℝ => D * Real.exp (-y))
      (MeasureTheory.volume.restrict (Set.Ioi 0))
    exact (integrableOn_exp_neg_Ioi 0).const_mul D
  have hsubset : Set.Ioc 0 L ⊆ Set.Ioi (0 : ℝ) :=
    Set.Ioc_subset_Ioi_self
  calc
    (∫ y in Set.Ioc 0 L,
        Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      ∫ y in Set.Ioc 0 L, D * Real.exp (-y) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with y
          exact Complex.normSq_nonneg _
        · exact hmajorInt.mono_set hsubset
        · filter_upwards with y
          exact normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half
            hdelta hdelta1 hdeltaPi hc hcEight hX hXpow y
    _ ≤ ∫ y in Set.Ioi (0 : ℝ), D * Real.exp (-y) := by
      apply MeasureTheory.setIntegral_mono_set hmajorInt
      · filter_upwards with y
        exact mul_nonneg hD0 (Real.exp_pos _).le
      · exact hsubset.eventuallyLE
    _ = D := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi_zero,
        mul_one]
    _ = delta ^ (-(1 / 2 : ℝ)) := rfl

theorem integral_normSq_selbergResidueInverseFourierKernel_div_sq_high_le
    {c delta L : ℝ} (hdelta : 0 < delta) (hdelta1 : delta ≤ 1)
    (hdeltaPi : delta < Real.pi / 2) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) {X : ℕ} (hX : 2 ≤ X)
    (hXpow : (X : ℝ) ≤ delta ^ (-c)) (hL : 0 < L) :
    (∫ y in Set.Ioi L,
      Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
        y ^ 2) ≤
      delta ^ (-(1 / 2 : ℝ)) / L ^ 2 := by
  let D : ℝ := delta ^ (-(1 / 2 : ℝ))
  have hD0 : 0 ≤ D := Real.rpow_nonneg hdelta.le _
  have hLsq : 0 < L ^ 2 := sq_pos_of_pos hL
  have hmajorInt : MeasureTheory.IntegrableOn
      (fun y : ℝ => (D / L ^ 2) * Real.exp (-y)) (Set.Ioi L) := by
    exact (integrableOn_exp_neg_Ioi L).const_mul (D / L ^ 2)
  calc
    (∫ y in Set.Ioi L,
        Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
          y ^ 2) ≤
      ∫ y in Set.Ioi L, (D / L ^ 2) * Real.exp (-y) := by
        apply MeasureTheory.integral_mono_of_nonneg
        · filter_upwards with y
          exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg y)
        · exact hmajorInt
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi]
            with y hy
          have hypos : 0 < y := hL.trans hy
          have hsq : L ^ 2 ≤ y ^ 2 :=
            (sq_le_sq₀ hL.le hypos.le).2 hy.le
          have hpoint :=
            normSq_selbergResidueInverseFourierKernel_le_exp_mul_delta_neg_half
              hdelta hdelta1 hdeltaPi hc hcEight hX hXpow y
          calc
            Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
                y ^ 2 ≤
              (D * Real.exp (-y)) / y ^ 2 :=
                div_le_div_of_nonneg_right hpoint (sq_nonneg y)
            _ ≤ (D * Real.exp (-y)) / L ^ 2 :=
              div_le_div_of_nonneg_left
                (mul_nonneg hD0 (Real.exp_pos _).le) hLsq hsq
            _ = (D / L ^ 2) * Real.exp (-y) := by ring
    _ = (D / L ^ 2) * Real.exp (-L) := by
      rw [MeasureTheory.integral_const_mul, integral_exp_neg_Ioi]
    _ ≤ D / L ^ 2 := by
      exact mul_le_of_le_one_right (div_nonneg hD0 hLsq.le)
        (Real.exp_le_one_iff.mpr (by linarith))
    _ = delta ^ (-(1 / 2 : ℝ)) / L ^ 2 := rfl

theorem exists_integral_normSq_selbergResidueInverseFourierKernel_low_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (_hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Set.Ioc 0 (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
            (selbergResidueInverseFourierKernel delta X y)) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) *
            Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  refine ⟨1 / a, by positivity, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi _hXexp hXpow hlogGtwo
  have hXone : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans hXone
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlogG : Real.log ((X : ℝ) ^ a) = a * Real.log (X : ℝ) :=
    Real.log_rpow hXpos a
  have hapos : 0 < a := by
    rw [hlogG] at hlogGtwo
    have hane : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at hlogGtwo
      norm_num at hlogGtwo
    exact lt_of_le_of_ne ha (Ne.symm hane)
  calc
    (∫ y in Set.Ioc 0 (Real.log ((X : ℝ) ^ a)),
        Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      delta ^ (-(1 / 2 : ℝ)) :=
        integral_normSq_selbergResidueInverseFourierKernel_low_le_delta_neg_half
          hdelta hdelta1 hdeltaPi hc hcEight hX hXpow
    _ = (1 / a) * (delta ^ (-(1 / 2 : ℝ)) *
          Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
      rw [hlogG]
      field_simp [hapos.ne', hlogX.ne']

theorem exists_integral_normSq_selbergResidueInverseFourierKernel_high_le
    {a c : ℝ} (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hcEight : c < 1 / 8) (_hac : (a + 2) * c ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) → (X : ℝ) ≤ delta ^ (-c) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Set.Ioi (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
              (selbergResidueInverseFourierKernel delta X y) /
            y ^ 2) ≤
          C * (delta ^ (-(1 / 2 : ℝ)) /
            (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  refine ⟨1 / a, by positivity, ?_⟩
  intro X delta hdelta hdelta1 hX hdeltaPi _hXexp hXpow hlogGtwo
  have hXone : 1 < (X : ℝ) := by exact_mod_cast (show 1 < X by omega)
  have hXpos : 0 < (X : ℝ) := zero_lt_one.trans hXone
  have hlogX : 0 < Real.log (X : ℝ) := Real.log_pos hXone
  have hlogG : Real.log ((X : ℝ) ^ a) = a * Real.log (X : ℝ) :=
    Real.log_rpow hXpos a
  have hapos : 0 < a := by
    rw [hlogG] at hlogGtwo
    have hane : a ≠ 0 := by
      intro ha0
      rw [ha0, zero_mul] at hlogGtwo
      norm_num at hlogGtwo
    exact lt_of_le_of_ne ha (Ne.symm hane)
  have hlogGpos : 0 < Real.log ((X : ℝ) ^ a) := by linarith
  calc
    (∫ y in Set.Ioi (Real.log ((X : ℝ) ^ a)),
        Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
          y ^ 2) ≤
      delta ^ (-(1 / 2 : ℝ)) /
        Real.log ((X : ℝ) ^ a) ^ 2 :=
          integral_normSq_selbergResidueInverseFourierKernel_div_sq_high_le
            hdelta hdelta1 hdeltaPi hc hcEight hX hXpow hlogGpos
    _ = (1 / a) * (delta ^ (-(1 / 2 : ℝ)) /
          (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
      rw [hlogG]
      field_simp [hapos.ne', hlogX.ne']

end HardyTheorem
