import PrimeNumberTheorem.CofinalExplicitFormula
import PrimeNumberTheorem.GlobalZeroCount
import PrimeNumberTheorem.PNTAsymptotics
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Filter Set Topology
open scoped BigOperators

namespace PrimeNumberTheorem
namespace ExplicitFormulaAux

/-- The proved classical zero-free region and the compact strip at low height
give one uniform real-part loss for every zero in a finite truncation. -/
theorem exists_nontrivialZero_re_le_one_sub_div_log_truncation :
    ∃ b : ℝ, 0 < b ∧ ∀ T : ℝ, 4 ≤ T →
      ∀ ρ ∈ nontrivialZerosFinset T,
        ρ.re ≤ 1 - b / Real.log (T + 6) := by
  rcases ZeroFreeRegion.classical_zero_free_region_proved with
    ⟨c, hc, hregion⟩
  rcases ZeroFreeRegion.classical_zero_free_region_compact 2 (by norm_num) with
    ⟨d, hd, hcompact⟩
  let b : ℝ := min c (d * Real.log 10)
  have hlogTen : 0 < Real.log (10 : ℝ) := Real.log_pos (by norm_num)
  have hb : 0 < b := lt_min hc (mul_pos hd hlogTen)
  refine ⟨b, hb, ?_⟩
  intro T hT ρ hρ
  rcases mem_nontrivialZerosFinset.mp hρ with ⟨hzero, himT⟩
  have hlogT : 0 < Real.log (T + 6) :=
    Real.log_pos (by linarith)
  by_cases hhigh : 2 ≤ |ρ.im|
  · have hlogIm : 0 < Real.log |ρ.im| :=
      ZeroFreeRegion.log_abs_pos_of_two_le hhigh
    have hlogMono : Real.log |ρ.im| ≤ Real.log (T + 6) := by
      apply Real.log_le_log
      · linarith
      · linarith
    have hb_le_c : b ≤ c := min_le_left _ _
    have hwidth : b / Real.log (T + 6) ≤ c / Real.log |ρ.im| := by
      calc
        b / Real.log (T + 6) ≤ c / Real.log (T + 6) :=
          div_le_div_of_nonneg_right hb_le_c hlogT.le
        _ ≤ c / Real.log |ρ.im| :=
          div_le_div_of_nonneg_left hc.le hlogIm hlogMono
    have hre : ρ.re < 1 - c / Real.log |ρ.im| := by
      by_contra hnot
      exact hregion ρ hhigh (le_of_not_gt hnot) hzero.1
    linarith
  · have himTwo : |ρ.im| ≤ 2 := (lt_of_not_ge hhigh).le
    have hb_le : b ≤ d * Real.log 10 := min_le_right _ _
    have hlogTenT : Real.log 10 ≤ Real.log (T + 6) := by
      apply Real.log_le_log
      · norm_num
      · linarith
    have hb_dlog : b ≤ d * Real.log (T + 6) :=
      hb_le.trans (mul_le_mul_of_nonneg_left hlogTenT hd.le)
    have hwidth : b / Real.log (T + 6) ≤ d :=
      (div_le_iff₀ hlogT).2 (by simpa [mul_comm] using hb_dlog)
    have hre : ρ.re < 1 - d := by
      by_contra hnot
      exact hcompact ρ himTwo (le_of_not_gt hnot) hzero.1
    linarith

/-- Unconditional finite-zero estimate obtained from the classical zero-free
region.  The constants are uniform in both the sample `x` and truncation
height `T`. -/
theorem
    exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq :
    ∃ b C : ℝ, 0 < b ∧ 0 ≤ C ∧ ∀ x T : ℝ, 1 < x → 4 ≤ T →
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2 := by
  classical
  rcases exists_nontrivialZero_re_le_one_sub_div_log_truncation with
    ⟨b, hb, hre⟩
  rcases exists_globalReciprocalZeroMultiplicity_le_log_sq with
    ⟨C, hC, hreciprocal⟩
  refine ⟨b, C, hb, hC, ?_⟩
  intro x T hx hT
  have hxpos : 0 < x := zero_lt_one.trans hx
  have hxnonneg : 0 ≤ x := hxpos.le
  let q : ℝ := 1 - b / Real.log (T + 6)
  unfold finiteNontrivialZeroSumWithMultiplicity
  calc
    ‖∑ ρ ∈ nontrivialZerosFinset T,
        (analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ ≤
        ∑ ρ ∈ nontrivialZerosFinset T,
          ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ :=
      norm_sum_le _ _
    _ ≤ ∑ ρ ∈ nontrivialZerosFinset T,
          x ^ q * ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      have hrpow : x ^ ρ.re ≤ x ^ q :=
        Real.rpow_le_rpow_of_exponent_le hx.le (by
          dsimp [q]
          exact hre T hT ρ hρ)
      have hmult : 0 ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) :=
        Nat.cast_nonneg _
      calc
        ‖(analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ / ρ‖ =
            (analyticOrderNatAt riemannZeta ρ : ℝ) *
              (x ^ ρ.re / ‖ρ‖) := by
          rw [mul_div_assoc, norm_mul, norm_zero_contribution_eq ρ hxpos]
          simp
        _ ≤ (analyticOrderNatAt riemannZeta ρ : ℝ) *
              (x ^ q / ‖ρ‖) := by
          exact mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right hrpow (norm_nonneg ρ)) hmult
        _ = x ^ q *
              ((analyticOrderNatAt riemannZeta ρ : ℝ) / ‖ρ‖) := by ring
    _ = x ^ q * globalReciprocalZeroMultiplicity T := by
      unfold globalReciprocalZeroMultiplicity
      rw [Finset.mul_sum]
    _ ≤ x ^ q * (C * (1 + Real.log (T + 6)) ^ 2) :=
      mul_le_mul_of_nonneg_left (hreciprocal T hT)
        (Real.rpow_nonneg hxnonneg q)
    _ = C * x ^ (1 - b / Real.log (T + 6)) *
          (1 + Real.log (T + 6)) ^ 2 := by
      dsimp [q]
      ring

set_option maxHeartbeats 1200000 in
/-- At the subpolynomial height `exp (a * sqrt (log m))`, all terms in the
moving-line explicit formula admit one de la Vallee Poussin error majorant. -/
theorem exists_nat_abs_chebyshevPsi0_sub_id_le_exp_sqrt_log :
    ∃ a C U : ℝ, 0 < a ∧ 0 ≤ C ∧ ∀ m : ℕ, 3 ≤ m →
      U ≤ Real.sqrt (Real.log (m : ℝ)) →
      |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * (m : ℝ) *
          ((Real.sqrt (Real.log (m : ℝ))) ^ 4 *
              Real.exp (-a * Real.sqrt (Real.log (m : ℝ))) +
            (Real.sqrt (Real.log (m : ℝ))) ^ 2 *
              Real.exp (-(1 / 2 : ℝ) *
                Real.sqrt (Real.log (m : ℝ)))) := by
  rcases
      exists_norm_finiteNontrivialZeroSumWithMultiplicity_le_zeroFree_mul_log_sq
      with ⟨b, Cz, hb, hCz, hzeros⟩
  rcases
      ExplicitFormulaResidues.exists_uniform_goodHeight_Icc_norm_nat_movingRight_truncatedExplicitFormula_sub_chebyshevPsi0_le
      with ⟨Cc, hCc, hcontour⟩
  let a : ℝ := min 1 b
  have ha : 0 < a := lt_min zero_lt_one hb
  have ha_one : a ≤ 1 := min_le_left _ _
  have ha_b : a ≤ b := min_le_right _ _
  let K0 : ℝ := ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
    ‖Complex.log Real.pi‖ +
    2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3) + Real.pi
  let Kl : ℝ := K0 + 4
  let Kd : ℝ := ‖deriv riemannZeta 0 / riemannZeta 0‖
  let C : ℝ := 13 * Cc + 4 * Kl + Kd + 9 * Cz
  let U : ℝ := max 1 (Real.log 8 / a)
  have hK0 : 0 ≤ K0 := by
    dsimp [K0]
    have hseries : 0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    positivity
  have hKl : 0 ≤ Kl := by dsimp [Kl]; positivity
  have hKd : 0 ≤ Kd := by dsimp [Kd]; positivity
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨a, C, U, ha, hC, ?_⟩
  intro m hm hU
  let x : ℝ := m
  let u : ℝ := Real.sqrt (Real.log x)
  let A : ℝ := Real.exp (a * u)
  have hx3 : (3 : ℝ) ≤ x := by dsimp [x]; exact_mod_cast hm
  have hx : 1 < x := by linarith
  have hxpos : 0 < x := by linarith
  have hxone : 1 ≤ x := by linarith
  have hlogx0 : 0 ≤ Real.log x := Real.log_nonneg hxone
  have hu0 : 0 ≤ u := by dsimp [u]; exact Real.sqrt_nonneg _
  have hUu : U ≤ u := by simpa [u, x] using hU
  have hu1 : 1 ≤ u := by
    exact (le_max_left 1 (Real.log 8 / a)).trans hUu
  have hu_pos : 0 < u := zero_lt_one.trans_le hu1
  have hu_sq : u ^ 2 = Real.log x := by
    dsimp [u]
    exact Real.sq_sqrt hlogx0
  have hlogEight : 0 < Real.log (8 : ℝ) := Real.log_pos (by norm_num)
  have hlogEight_le : Real.log 8 ≤ a * u := by
    have hdiv : Real.log 8 / a ≤ u :=
      (le_max_right 1 (Real.log 8 / a)).trans hUu
    simpa [mul_comm] using (div_le_iff₀ ha).mp hdiv
  have hau0 : 0 ≤ a * u := mul_nonneg ha.le hu0
  have hApos : 0 < A := by dsimp [A]; positivity
  have hAone : 1 ≤ A := by
    dsimp [A]
    exact Real.one_le_exp hau0
  have hA8 : 8 ≤ A := by
    calc
      (8 : ℝ) = Real.exp (Real.log 8) := by rw [Real.exp_log (by norm_num)]
      _ ≤ Real.exp (a * u) := Real.exp_le_exp.mpr hlogEight_le
      _ = A := rfl
  have hau_le_usq : a * u ≤ u ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha_one) hu0,
      mul_nonneg (sub_nonneg.mpr hu1) hu0]
  have hA_le_x : A ≤ x := by
    calc
      A = Real.exp (a * u) := rfl
      _ ≤ Real.exp (u ^ 2) := Real.exp_le_exp.mpr hau_le_usq
      _ = x := by rw [hu_sq, Real.exp_log hxpos]
  rcases hcontour A hA8 with ⟨T, hTmem, hgood, hformula⟩
  have hTpos : 0 < T := hApos.trans_le hTmem.1
  have hT4 : 4 ≤ T := by linarith [hA8, hTmem.1]
  have hT_le_two_x : T ≤ 2 * x := by
    calc
      T ≤ A + 1 := hTmem.2
      _ ≤ 2 * A := by linarith
      _ ≤ 2 * x := mul_le_mul_of_nonneg_left hA_le_x (by norm_num)
  have hTplus : T + 6 ≤ 8 * A := by
    calc
      T + 6 ≤ A + 7 := by linarith [hTmem.2]
      _ ≤ 8 * A := by nlinarith
  have hAplus : A + 6 ≤ 8 * A := by nlinarith
  have hlogA : Real.log A = a * u := by simp [A]
  have hlogEightA : Real.log (8 * A) = Real.log 8 + a * u := by
    rw [Real.log_mul (by norm_num) hApos.ne', hlogA]
  have hlogTplus : Real.log (T + 6) ≤ 2 * a * u := by
    have hlog := Real.log_le_log (by linarith) hTplus
    rw [hlogEightA] at hlog
    linarith
  have hlogAplus : Real.log (A + 6) ≤ 2 * a * u := by
    have hlog := Real.log_le_log (by positivity) hAplus
    rw [hlogEightA] at hlog
    linarith
  have hlogTpos : 0 < Real.log (T + 6) := Real.log_pos (by linarith)
  have hLm0 : 0 ≤ 1 + Real.log x := by linarith
  have hLA0 : 0 ≤ 1 + Real.log (A + 6) := by
    have := Real.log_nonneg (by linarith : 1 ≤ A + 6)
    linarith
  have hLT0 : 0 ≤ 1 + Real.log (T + 6) := by linarith
  have hLm : 1 + Real.log x ≤ 2 * u ^ 2 := by
    rw [← hu_sq]
    nlinarith [sq_nonneg (u - 1)]
  have hLA : 1 + Real.log (A + 6) ≤ 3 * u := by
    have hau_le_u : a * u ≤ u :=
      mul_le_of_le_one_left hu0 ha_one
    linarith
  have hLT : 1 + Real.log (T + 6) ≤ 3 * u := by
    have hau_le_u : a * u ≤ u :=
      mul_le_of_le_one_left hu0 ha_one
    linarith
  have hu2_le_u4 : u ^ 2 ≤ u ^ 4 := by
    nlinarith [sq_nonneg (u ^ 2 - 1)]
  have hlogSquares :
      (1 + Real.log x) ^ 2 + (1 + Real.log (A + 6)) ^ 2 ≤
        13 * u ^ 4 := by
    have hLmSq : (1 + Real.log x) ^ 2 ≤ 4 * u ^ 4 := by nlinarith
    have hLASq : (1 + Real.log (A + 6)) ^ 2 ≤ 9 * u ^ 2 := by nlinarith
    nlinarith
  have hmain :
      Cc * x * ((1 + Real.log x) ^ 2 +
          (1 + Real.log (A + 6)) ^ 2) / T ≤
        13 * Cc * x * u ^ 4 * Real.exp (-a * u) := by
    calc
      Cc * x * ((1 + Real.log x) ^ 2 +
          (1 + Real.log (A + 6)) ^ 2) / T ≤
          Cc * x * (13 * u ^ 4) / T := by
        apply div_le_div_of_nonneg_right _ hTpos.le
        exact mul_le_mul_of_nonneg_left hlogSquares
          (mul_nonneg hCc hxpos.le)
      _ ≤ Cc * x * (13 * u ^ 4) / A := by
        exact div_le_div_of_nonneg_left (by positivity) hApos hTmem.1
      _ = 13 * Cc * x * u ^ 4 * Real.exp (-a * u) := by
        dsimp [A]
        rw [div_eq_mul_inv, ← Real.exp_neg]
        ring
  have hwidth : 1 / (2 * u) ≤ b / Real.log (T + 6) := by
    have hden : Real.log (T + 6) ≤ 2 * a * u := hlogTplus
    have htwoau : 0 < 2 * a * u := by positivity
    calc
      1 / (2 * u) = a / (2 * a * u) := by field_simp [ha.ne', hu_pos.ne']
      _ ≤ a / Real.log (T + 6) :=
        div_le_div_of_nonneg_left ha.le hlogTpos hden
      _ ≤ b / Real.log (T + 6) :=
        div_le_div_of_nonneg_right ha_b hlogTpos.le
  have hq : 1 - b / Real.log (T + 6) ≤ 1 - 1 / (2 * u) := by linarith
  have hrpow :
      x ^ (1 - b / Real.log (T + 6)) ≤
        x * Real.exp (-(1 / 2 : ℝ) * u) := by
    calc
      x ^ (1 - b / Real.log (T + 6)) ≤ x ^ (1 - 1 / (2 * u)) :=
        Real.rpow_le_rpow_of_exponent_le hxone hq
      _ = x * Real.exp (-(1 / 2 : ℝ) * u) := by
        rw [Real.rpow_def_of_pos hxpos]
        have hexponent :
            Real.log x * (1 - 1 / (2 * u)) = u ^ 2 - u / 2 := by
          rw [← hu_sq]
          field_simp [hu_pos.ne']
        rw [hexponent, show u ^ 2 - u / 2 = u ^ 2 + (-(1 / 2 : ℝ) * u) by ring,
          Real.exp_add, hu_sq, Real.exp_log hxpos]
  have hzero0 := hzeros x T hx hT4
  have hzero :
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
        9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := by
    calc
      ‖finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
          Cz * x ^ (1 - b / Real.log (T + 6)) *
            (1 + Real.log (T + 6)) ^ 2 := hzero0
      _ ≤ Cz * (x * Real.exp (-(1 / 2 : ℝ) * u)) *
            (3 * u) ^ 2 := by gcongr
      _ = 9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := by ring
  have hlogTfour : Real.log (T + 4) ≤ 2 * a * u := by
    have hmono : Real.log (T + 4) ≤ Real.log (T + 6) :=
      Real.log_le_log (by linarith) (by linarith)
    exact hmono.trans hlogTplus
  have hcoeff :
      ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
        ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (T + 4)) + Real.pi ≤ Kl * u := by
    have hau_le_u : a * u ≤ u :=
      mul_le_of_le_one_left hu0 ha_one
    dsimp [Kl, K0]
    nlinarith [mul_nonneg hK0 (sub_nonneg.mpr hu1)]
  let left : ℝ :=
    ((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
      ‖Complex.log Real.pi‖ +
      2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
        Real.log (T + 4)) + Real.pi) * x ^ (-1 : ℝ)) * (2 * T) /
      (2 * Real.pi)
  have hcoeff0 :
      0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
        ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (T + 4)) + Real.pi := by
    have hlog0 : 0 ≤ Real.log (T + 4) :=
      Real.log_nonneg (by linarith)
    have hseries : 0 ≤ ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 :=
      tsum_nonneg fun n => norm_nonneg _
    positivity
  have hinv_mul_T : x ^ (-1 : ℝ) * T ≤ 2 := by
    rw [Real.rpow_neg_one]
    exact (inv_mul_le_iff₀ hxpos).2 (by simpa [mul_comm] using hT_le_two_x)
  have hleft0 : 0 ≤ left := by dsimp [left]; positivity
  have hleft : left ≤ 4 * Kl * u := by
    have hnum0 :
        0 ≤ ((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
          ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (T + 4)) + Real.pi) * x ^ (-1 : ℝ)) * (2 * T) := by
      positivity
    have hpi : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
    have hdrop : left ≤
        ((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
          ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (T + 4)) + Real.pi) * x ^ (-1 : ℝ)) * (2 * T) := by
      dsimp [left]
      exact div_le_self hnum0 hpi
    apply hdrop.trans
    calc
      ((ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
        ‖Complex.log Real.pi‖ +
          2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
            Real.log (T + 4)) + Real.pi) * x ^ (-1 : ℝ)) * (2 * T) =
          2 * (ExplicitFormulaResidues.vonMangoldtLSeriesNorm 1 +
            ‖Complex.log Real.pi‖ +
            2 * (‖(Real.eulerMascheroniConstant : ℂ)‖ + 3 +
              Real.log (T + 4)) + Real.pi) * (x ^ (-1 : ℝ) * T) := by ring
      _ ≤ 2 * (Kl * u) * 2 := by gcongr
      _ = 4 * Kl * u := by ring
  let approx : ℂ :=
    (((x : ℂ) - deriv riemannZeta 0 / riemannZeta 0 +
      ∑ ρ ∈ nontrivialZerosFinset T,
        -((analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ) / ρ) -
        (chebyshevPsi0 x : ℂ))
  have hformula0 := hformula m 0 hm
  have hformula' :
      ‖approx‖ ≤
        Cc * x * ((1 + Real.log x) ^ 2 +
          (1 + Real.log (A + 6)) ^ 2) / T + left := by
    have hformula1 := hformula0
    simp [finiteTrivialZeroSum] at hformula1
    simpa [approx, x, left] using hformula1
  have hformulaClean :
      ‖approx‖ ≤ 13 * Cc * x * u ^ 4 * Real.exp (-a * u) +
        4 * Kl * u :=
    hformula'.trans (add_le_add hmain hleft)
  have hxe : 1 ≤ x * Real.exp (-a * u) := by
    have hdiff : 0 ≤ u ^ 2 - a * u := by linarith
    calc
      (1 : ℝ) ≤ Real.exp (u ^ 2 - a * u) := Real.one_le_exp hdiff
      _ = x * Real.exp (-a * u) := by
        rw [show u ^ 2 - a * u = u ^ 2 + (-a * u) by ring,
          Real.exp_add, hu_sq, Real.exp_log hxpos]
  have hu_le_u4 : u ≤ u ^ 4 := by
    have hp := pow_le_pow_right₀ hu1 (by norm_num : (1 : ℕ) ≤ 4)
    simpa using hp
  have hleftScale : 4 * Kl * u ≤
      4 * Kl * x * u ^ 4 * Real.exp (-a * u) := by
    have hscale : u ≤ x * u ^ 4 * Real.exp (-a * u) := by
      calc
        u ≤ u ^ 4 := hu_le_u4
        _ ≤ u ^ 4 * (x * Real.exp (-a * u)) :=
          le_mul_of_one_le_right (pow_nonneg hu0 4) hxe
        _ = x * u ^ 4 * Real.exp (-a * u) := by ring
    simpa [mul_assoc] using
      (mul_le_mul_of_nonneg_left hscale
        (show 0 ≤ 4 * Kl by positivity))
  have hderivScale : Kd ≤ Kd * x * u ^ 4 * Real.exp (-a * u) := by
    have hu4one : 1 ≤ u ^ 4 := by
      have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hu1 4
      simpa using hp
    have hscale : 1 ≤ x * u ^ 4 * Real.exp (-a * u) := by
      calc
        (1 : ℝ) ≤ u ^ 4 := hu4one
        _ ≤ u ^ 4 * (x * Real.exp (-a * u)) :=
          le_mul_of_one_le_right (pow_nonneg hu0 4) hxe
        _ = x * u ^ 4 * Real.exp (-a * u) := by ring
    calc
      Kd = Kd * 1 := by ring
      _ ≤ Kd * (x * u ^ 4 * Real.exp (-a * u)) :=
        mul_le_mul_of_nonneg_left hscale hKd
      _ = Kd * x * u ^ 4 * Real.exp (-a * u) := by ring
  have hdecomp :
      ((chebyshevPsi0 x - x : ℝ) : ℂ) =
        -(deriv riemannZeta 0 / riemannZeta 0) -
          finiteNontrivialZeroSumWithMultiplicity x T - approx := by
    have hzeroSum :
        (∑ ρ ∈ nontrivialZerosFinset T,
            -((analyticOrderNatAt riemannZeta ρ : ℂ) * (x : ℂ) ^ ρ) / ρ) =
          -finiteNontrivialZeroSumWithMultiplicity x T := by
      unfold finiteNontrivialZeroSumWithMultiplicity
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro ρ hρ
      ring
    dsimp [approx]
    rw [hzeroSum]
    push_cast
    ring
  change |chebyshevPsi0 x - x| ≤ C * x *
    (u ^ 4 * Real.exp (-a * u) +
      u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u))
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hdecomp]
  have htotal :
      ‖-(deriv riemannZeta 0 / riemannZeta 0) -
          finiteNontrivialZeroSumWithMultiplicity x T - approx‖ ≤
        (13 * Cc + 4 * Kl + Kd) * x * u ^ 4 * Real.exp (-a * u) +
          9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := by
    calc
      _ ≤ (Kd + ‖finiteNontrivialZeroSumWithMultiplicity x T‖) + ‖approx‖ := by
        calc
          _ ≤ ‖-(deriv riemannZeta 0 / riemannZeta 0) -
                finiteNontrivialZeroSumWithMultiplicity x T‖ + ‖approx‖ :=
            norm_sub_le _ _
          _ ≤ (Kd + ‖finiteNontrivialZeroSumWithMultiplicity x T‖) +
                ‖approx‖ := by
            gcongr
            calc
              ‖-(deriv riemannZeta 0 / riemannZeta 0) -
                  finiteNontrivialZeroSumWithMultiplicity x T‖ ≤
                  ‖-(deriv riemannZeta 0 / riemannZeta 0)‖ +
                    ‖finiteNontrivialZeroSumWithMultiplicity x T‖ :=
                norm_sub_le _ _
              _ = Kd + ‖finiteNontrivialZeroSumWithMultiplicity x T‖ := by
                simp [Kd]
      _ ≤ (Kd * x * u ^ 4 * Real.exp (-a * u) +
              9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u)) +
            (13 * Cc * x * u ^ 4 * Real.exp (-a * u) +
              4 * Kl * x * u ^ 4 * Real.exp (-a * u)) := by
        exact add_le_add (add_le_add hderivScale hzero)
          (hformulaClean.trans (add_le_add_right hleftScale _))
      _ = (13 * Cc + 4 * Kl + Kd) * x * u ^ 4 * Real.exp (-a * u) +
          9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) := by
        ring
  apply htotal.trans
  have hlead0 : 0 ≤ 13 * Cc + 4 * Kl + Kd := by positivity
  let cross : ℝ :=
      9 * Cz * x * u ^ 4 * Real.exp (-a * u) +
        (13 * Cc + 4 * Kl + Kd) * x * u ^ 2 *
          Real.exp (-(1 / 2 : ℝ) * u)
  have hcross : 0 ≤ cross := by
    dsimp [cross]
    exact add_nonneg (by positivity) (by positivity)
  calc
    (13 * Cc + 4 * Kl + Kd) * x * u ^ 4 * Real.exp (-a * u) +
        9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u) ≤
      ((13 * Cc + 4 * Kl + Kd) * x * u ^ 4 * Real.exp (-a * u) +
        9 * Cz * x * u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u)) + cross :=
      le_add_of_nonneg_right hcross
    _ = C * x * (u ^ 4 * Real.exp (-a * u) +
        u ^ 2 * Real.exp (-(1 / 2 : ℝ) * u)) := by
      dsimp [C, cross]
      ring

/-- The moving-height explicit formula and the classical zero-free region imply
the prime number theorem along natural arguments. -/
theorem chebyshevPsi0_sub_id_nat_isLittleO :
    (fun m : ℕ => chebyshevPsi0 (m : ℝ) - (m : ℝ))
      =o[Filter.atTop] (fun m : ℕ => (m : ℝ)) := by
  rcases exists_nat_abs_chebyshevPsi0_sub_id_le_exp_sqrt_log with
    ⟨a, C, U, ha, hC, hbound⟩
  have hfour :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero a ha 4
  have htwo :=
    tendsto_pntSqrtLog_pow_mul_exp_neg_mul_atTop_nhds_zero
      (1 / 2 : ℝ) (by norm_num) 2
  have hmajorant :
      Filter.Tendsto (fun m : ℕ =>
        C * (pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) +
          pntSqrtLog m ^ 2 * Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m)))
        Filter.atTop (nhds 0) := by
    simpa only [zero_add, mul_zero] using (hfour.add htwo).const_mul C
  refine Asymptotics.isLittleO_iff.2 ?_
  intro ε hε
  have hmajorant_lt : ∀ᶠ m : ℕ in Filter.atTop,
      C * (pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) +
        pntSqrtLog m ^ 2 * Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m)) < ε :=
    (tendsto_order.1 hmajorant).2 ε hε
  have hU : ∀ᶠ m : ℕ in Filter.atTop, U ≤ pntSqrtLog m :=
    (tendsto_atTop.1 tendsto_pntSqrtLog_atTop U)
  filter_upwards [eventually_ge_atTop 3, hU, hmajorant_lt] with m hm hUm hmaj
  have hpoint := hbound m hm (by simpa only [pntSqrtLog] using hUm)
  rw [Real.norm_eq_abs]
  calc
    |chebyshevPsi0 (m : ℝ) - (m : ℝ)| ≤
        C * (m : ℝ) *
          (pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) +
            pntSqrtLog m ^ 2 * Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m)) := by
      simpa only [pntSqrtLog] using hpoint
    _ = (m : ℝ) *
        (C * (pntSqrtLog m ^ 4 * Real.exp (-a * pntSqrtLog m) +
          pntSqrtLog m ^ 2 * Real.exp (-(1 / 2 : ℝ) * pntSqrtLog m))) := by
      ring
    _ ≤ (m : ℝ) * ε :=
      mul_le_mul_of_nonneg_left hmaj.le (Nat.cast_nonneg m)
    _ = ε * ‖(m : ℝ)‖ := by simp [mul_comm]

end ExplicitFormulaAux
end PrimeNumberTheorem
