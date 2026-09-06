import HardyTheorem.SelbergMomentSpecialization
import HardyTheorem.SelbergRefinedUniformSecondMoment

open Complex Filter MeasureTheory Set
open scoped Interval

namespace HardyTheorem

/-!
# Positive measure of Selberg strict-cancellation windows

The short-window exponent is chosen only after the uniform nonconstant S2
coefficient is known.  The explicit `X^4` residue is absorbed separately
using `X=floor(T^(1/32))`.
-/

/-- The final short-window exponent selected after the S2 coefficient. -/
noncomputable def selbergStrictCancellationExponent (c₁ C : ℝ) : ℝ :=
  min 1 (c₁ ^ 2 * Real.pi / (8 * (C + 1)))

theorem selbergStrictCancellationExponent_pos
    {c₁ C : ℝ} (hc₁ : 0 < c₁) (hC : 0 ≤ C) :
    0 < selbergStrictCancellationExponent c₁ C := by
  unfold selbergStrictCancellationExponent
  exact lt_min zero_lt_one (by positivity)

theorem selbergStrictCancellationExponent_le_one (c₁ C : ℝ) :
    selbergStrictCancellationExponent c₁ C ≤ 1 := by
  exact min_le_left _ _

theorem four_mul_selbergStrictCancellationExponent_mul_le
    {c₁ C : ℝ} (hc₁ : 0 < c₁) (hC : 0 ≤ C) :
    4 * selbergStrictCancellationExponent c₁ C * C ≤ c₁ ^ 2 * Real.pi := by
  let a := selbergStrictCancellationExponent c₁ C
  have ha : 0 < a := selbergStrictCancellationExponent_pos hc₁ hC
  have haUpper : a ≤ c₁ ^ 2 * Real.pi / (8 * (C + 1)) := by
    exact min_le_right _ _
  have hden : 0 < 8 * (C + 1) := by positivity
  have hscaled : 8 * (C + 1) * a ≤ c₁ ^ 2 * Real.pi := by
    have hraw := (le_div_iff₀ hden).mp haUpper
    simpa [mul_comm, mul_left_comm, mul_assoc] using hraw
  have hpi : 0 < c₁ ^ 2 * Real.pi := by positivity
  dsimp only [a] at ha hscaled ⊢
  nlinarith

/-- The uniform nonconstant S2 term consumes at most one eighth of the
square first-moment budget. -/
theorem selberg_nonconstant_secondMoment_le_eighth
    {a C c₁ H logX Y : ℝ}
    (ha : 0 < a) (_hC : 0 ≤ C) (hc₁ : 0 < c₁)
    (hlogX : 0 < logX) (hY : 0 ≤ Y)
    (hH : H = 2 * Real.pi / (a * logX))
    (hchoose : 4 * a * C ≤ c₁ ^ 2 * Real.pi) :
    C * (H * Y / logX) ≤ (c₁ ^ 2 / 8) * (H ^ 2 * Y) := by
  have hfoura : 0 < 4 * a := by positivity
  have hCa : C ≤ c₁ ^ 2 * Real.pi / (4 * a) := by
    exact (le_div_iff₀ hfoura).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hchoose)
  have hcoeff : C / logX ≤ c₁ ^ 2 / 8 * H := by
    calc
      C / logX ≤ (c₁ ^ 2 * Real.pi / (4 * a)) / logX :=
        div_le_div_of_nonneg_right hCa hlogX.le
      _ = c₁ ^ 2 / 8 * H := by
        rw [hH]
        field_simp [ha.ne', hlogX.ne']
        ring
  have hHnonneg : 0 ≤ H := by rw [hH]; positivity
  calc
    C * (H * Y / logX) = (C / logX) * (H * Y) := by ring
    _ ≤ (c₁ ^ 2 / 8 * H) * (H * Y) :=
      mul_le_mul_of_nonneg_right hcoeff (mul_nonneg hHnonneg hY)
    _ = (c₁ ^ 2 / 8) * (H ^ 2 * Y) := by ring

/-- The actual residue `20*X^4` is eventually at most one eighth of the
square first-moment budget. -/
theorem eventually_twenty_selbergFirstMomentCutoff_fourth_le_eighth_sqrt
    {c₁ : ℝ} (hc₁ : 0 < c₁) :
    ∀ᶠ T : ℝ in atTop,
      20 * (selbergFirstMomentCutoff T : ℝ) ^ 4 ≤
        (c₁ ^ 2 / 8) * T ^ (1 / 2 : ℝ) := by
  have hbase := eventually_log_div_sixtyFour_le_log_selbergFirstMomentCutoff
  have hgrow : ∀ᶠ T : ℝ in atTop,
      160 / c₁ ^ 2 ≤ T ^ (3 / 8 : ℝ) :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 3 / 8)).eventually_ge_atTop
      (160 / c₁ ^ 2)
  filter_upwards [hbase, hgrow] with T hbaseT hgrowT
  rcases hbaseT with ⟨hTpos, _hlog, hXupper⟩
  have hXfourth : (selbergFirstMomentCutoff T : ℝ) ^ 4 ≤
      T ^ (1 / 8 : ℝ) := by
    calc
      (selbergFirstMomentCutoff T : ℝ) ^ 4 ≤
          (T ^ (1 / 32 : ℝ)) ^ 4 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hXupper 4
      _ = (T ^ (1 / 32 : ℝ)) ^ (4 : ℝ) := by
        exact (Real.rpow_natCast _ 4).symm
      _ = T ^ ((1 / 32 : ℝ) * 4) := by
        rw [← Real.rpow_mul hTpos.le]
      _ = T ^ (1 / 8 : ℝ) := by norm_num
  have hpowProduct :
      T ^ (1 / 8 : ℝ) * T ^ (3 / 8 : ℝ) = T ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hTpos]
    norm_num
  have hdom :
      20 * T ^ (1 / 8 : ℝ) ≤
        (c₁ ^ 2 / 8) * T ^ (1 / 2 : ℝ) := by
    calc
      20 * T ^ (1 / 8 : ℝ) =
          (c₁ ^ 2 / 8 * T ^ (1 / 8 : ℝ)) * (160 / c₁ ^ 2) := by
        field_simp [hc₁.ne']
        ring
      _ ≤ (c₁ ^ 2 / 8 * T ^ (1 / 8 : ℝ)) * T ^ (3 / 8 : ℝ) :=
        mul_le_mul_of_nonneg_left hgrowT (by positivity)
      _ = (c₁ ^ 2 / 8) *
          (T ^ (1 / 8 : ℝ) * T ^ (3 / 8 : ℝ)) := by ring
      _ = (c₁ ^ 2 / 8) * T ^ (1 / 2 : ℝ) := by rw [hpowProduct]
  exact (mul_le_mul_of_nonneg_left hXfourth (by norm_num : (0 : ℝ) ≤ 20)).trans hdom

/-- Selberg S5: for one fixed exponent chosen after the uniform S2
coefficient, strict-cancellation starts occupy a positive proportion of
`[0,T]`. -/
theorem exists_pos_measure_strictCancellationStarts_selberg :
    ∃ a κ T0 : ℝ, 0 < a ∧ a ≤ 1 ∧ 0 < κ ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T →
        let X := selbergFirstMomentCutoff T
        let H := selbergMomentWindow a T
        let F := selbergCompletedMollifiedF (1 / T) X
        κ * T ≤ volume.real
          (Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) := by
  obtain ⟨CN, hCN, hS2⟩ :=
    exists_integral_normSq_sliding_selbergCompletedMollifiedF_le_refined_uniform
  obtain ⟨c₁, Tfirst, hc₁, hTfirst, hS4⟩ :=
    exists_pos_rpow_three_quarters_selbergSlidingFirstMoment_lower
  let a := selbergStrictCancellationExponent c₁ CN
  have ha : 0 < a := selbergStrictCancellationExponent_pos hc₁ hCN
  have haOne : a ≤ 1 := selbergStrictCancellationExponent_le_one c₁ CN
  have hchoose : 4 * a * CN ≤ c₁ ^ 2 * Real.pi :=
    four_mul_selbergStrictCancellationExponent_mul_le hc₁ hCN
  have hac : (a + 2) * (1 / 32 : ℝ) ≤ 1 / 4 := by
    nlinarith
  obtain ⟨C3raw, hC3raw, hS3⟩ :=
    exists_integral_sq_abs_selbergCompletedMollifiedF_sliding_le
      ha.le (by norm_num : (0 : ℝ) ≤ 1 / 32)
      (by norm_num : (1 / 32 : ℝ) < 1 / 8) hac
  let C3 : ℝ := 64 * C3raw + 1
  have hC3 : 0 < C3 := by dsimp [C3]; positivity
  let κ : ℝ := c₁ ^ 2 / (4 * C3)
  have hκ : 0 < κ := by dsimp [κ]; positivity
  have hparam := eventually_selbergMomentParameter_conditions ha
  obtain ⟨Tparam, hparamAfter⟩ := eventually_atTop.1 hparam
  have hresidue :=
    eventually_twenty_selbergFirstMomentCutoff_fourth_le_eighth_sqrt hc₁
  obtain ⟨Tresidue, hresidueAfter⟩ := eventually_atTop.1 hresidue
  let T0 := max Tfirst (max Tparam Tresidue)
  refine ⟨a, κ, T0, ha, haOne, hκ,
    hTfirst.trans (le_max_left _ _), ?_⟩
  intro T hT
  have hTfirst' : Tfirst ≤ T := (le_max_left _ _).trans hT
  have hTparam' : Tparam ≤ T :=
    (le_max_left Tparam Tresidue).trans ((le_max_right Tfirst _).trans hT)
  have hTresidue' : Tresidue ≤ T :=
    (le_max_right Tparam Tresidue).trans ((le_max_right Tfirst _).trans hT)
  rcases hparamAfter T hTparam' with
    ⟨hdelta, hdeltaOne, hdeltaPi, hXtwo, hXexp, hXpow,
      hlogXa, hlogDelta, hlogRatio, hH, hHT⟩
  have hresidueT := hresidueAfter T hTresidue'
  let X := selbergFirstMomentCutoff T
  let H := selbergMomentWindow a T
  let F := selbergCompletedMollifiedF (1 / T) X
  let MS := (c₁ ^ 2 / 4) * (H ^ 2 * T ^ (1 / 2 : ℝ))
  let MA := C3 * (H ^ 2 * T ^ (1 / 2 : ℝ))
  have hTpos : 0 < T := one_div_pos.mp hdelta
  have hdeltaHalf : (1 / T) ^ (-(1 / 2 : ℝ)) =
      T ^ (1 / 2 : ℝ) := by
    rw [Real.rpow_neg_eq_inv_rpow]
    congr 1
    field_simp
  have hInvDelta : 1 / (1 / T) = T := by field_simp
  have hlogX : 0 < Real.log (X : ℝ) :=
    Real.log_pos (lt_of_lt_of_le (by norm_num) hXexp)
  have hlogRpow : Real.log ((X : ℝ) ^ a) =
      a * Real.log (X : ℝ) := Real.log_rpow (by positivity) a
  have hHform : H = 2 * Real.pi / (a * Real.log (X : ℝ)) := by
    dsimp [H, selbergMomentWindow]
    rw [hlogRpow]
  have hS2T := hS2 a ha haOne X (1 / T) 0 T hdelta hdeltaOne hXtwo
    hdeltaPi hXexp hXpow hlogXa hTpos.le
  have hS2real :
      (∫ t in 0..T, (MathlibAux.slidingSignedAbsMass F H t) ^ 2) ≤
        20 * (H ^ 2 * (X : ℝ) ^ 4) +
          CN * (H * T ^ (1 / 2 : ℝ) / Real.log (X : ℝ)) := by
    simpa only [X, H, F, selbergMomentWindow,
      MathlibAux.slidingSignedAbsMass,
      MathlibAux.slidingWindowMass,
      normSq_interval_selbergCompletedMollifiedFComplex_eq_sq_abs,
      hdeltaHalf] using hS2T
  have hResiduePart :
      20 * (H ^ 2 * (X : ℝ) ^ 4) ≤
        (c₁ ^ 2 / 8) * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by
    calc
      20 * (H ^ 2 * (X : ℝ) ^ 4) =
          H ^ 2 * (20 * (X : ℝ) ^ 4) := by ring
      _ ≤ H ^ 2 * ((c₁ ^ 2 / 8) * T ^ (1 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_left (by simpa only [X] using hresidueT)
          (sq_nonneg H)
      _ = (c₁ ^ 2 / 8) * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by ring
  have hNonconstantPart :
      CN * (H * T ^ (1 / 2 : ℝ) / Real.log (X : ℝ)) ≤
        (c₁ ^ 2 / 8) * (H ^ 2 * T ^ (1 / 2 : ℝ)) :=
    selberg_nonconstant_secondMoment_le_eighth ha hCN hc₁ hlogX
      (Real.rpow_nonneg hTpos.le _) hHform hchoose
  have hMS : 0 ≤ MS := by dsimp [MS]; positivity
  have hS2MS :
      (∫ t in 0..T, (MathlibAux.slidingSignedAbsMass F H t) ^ 2) ≤ MS := by
    calc
      _ ≤ 20 * (H ^ 2 * (X : ℝ) ^ 4) +
          CN * (H * T ^ (1 / 2 : ℝ) / Real.log (X : ℝ)) := hS2real
      _ ≤ (c₁ ^ 2 / 8) * (H ^ 2 * T ^ (1 / 2 : ℝ)) +
          (c₁ ^ 2 / 8) * (H ^ 2 * T ^ (1 / 2 : ℝ)) :=
        add_le_add hResiduePart hNonconstantPart
      _ = MS := by dsimp [MS]; ring
  have hS3T := hS3 X (1 / T) H hdelta hdeltaOne hXtwo hdeltaPi
    hXexp hXpow hlogDelta hH.le
  have hS3raw :
      (∫ t : ℝ, (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ≤
        C3raw * (H ^ 2 *
          (T ^ (1 / 2 : ℝ) * Real.log T / Real.log (X : ℝ))) := by
    simpa only [X, H, F, MathlibAux.slidingAbsoluteMass,
      MathlibAux.slidingWindowMass,
      norm_selbergCompletedMollifiedFComplex_eq_abs,
      hdeltaHalf, hInvDelta] using hS3T
  have hratio : Real.log T / Real.log (X : ℝ) ≤ 64 := by
    simpa only [X, hInvDelta] using hlogRatio
  have hS3bound :
      (∫ t : ℝ, (MathlibAux.slidingAbsoluteMass F H t) ^ 2) ≤ MA := by
    calc
      _ ≤ C3raw * (H ^ 2 *
          (T ^ (1 / 2 : ℝ) * Real.log T / Real.log (X : ℝ))) := hS3raw
      _ ≤ C3raw * (H ^ 2 * (T ^ (1 / 2 : ℝ) * 64)) := by
        gcongr
        rw [show T ^ (1 / 2 : ℝ) * Real.log T / Real.log (X : ℝ) =
          T ^ (1 / 2 : ℝ) * (Real.log T / Real.log (X : ℝ)) by ring]
        exact mul_le_mul_of_nonneg_left hratio
          (Real.rpow_nonneg hTpos.le _)
      _ ≤ C3 * (H ^ 2 * T ^ (1 / 2 : ℝ)) := by
        dsimp [C3]
        have hbaseNonneg : 0 ≤ H ^ 2 * T ^ (1 / 2 : ℝ) := by positivity
        nlinarith
      _ = MA := rfl
  have hS4real :
      c₁ * (H * T ^ (3 / 4 : ℝ)) ≤
        ∫ t in 0..T, MathlibAux.slidingAbsoluteMass F H t := by
    simpa only [X, H, F, MathlibAux.slidingAbsoluteMass,
      MathlibAux.slidingWindowMass] using hS4 T H hTfirst' hH.le hHT
  have hAbsInt : Integrable
      (fun t => (MathlibAux.slidingAbsoluteMass F H t) ^ 2) :=
    integrable_sq_slidingAbsoluteMass_selbergCompletedMollifiedF
      hdelta hdeltaPi X hH.le
  let B : ℝ := c₁ / 2 * (H * T ^ (3 / 4 : ℝ))
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpow : (T ^ (3 / 4 : ℝ)) ^ 2 =
      T * T ^ (1 / 2 : ℝ) := by
    calc
      (T ^ (3 / 4 : ℝ)) ^ 2 =
          T ^ (3 / 4 : ℝ) * T ^ (3 / 4 : ℝ) := pow_two _
      _ = T ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_add hTpos]
        norm_num
      _ = T ^ (1 : ℝ) * T ^ (1 / 2 : ℝ) := by
        rw [← Real.rpow_add hTpos]
        norm_num
      _ = T * T ^ (1 / 2 : ℝ) := by rw [Real.rpow_one]
  have hinside : T * MS = B ^ 2 := by
    calc
      T * MS = c₁ ^ 2 / 4 * H ^ 2 *
          (T * T ^ (1 / 2 : ℝ)) := by dsimp [MS]; ring
      _ = c₁ ^ 2 / 4 * H ^ 2 * (T ^ (3 / 4 : ℝ)) ^ 2 := by
        rw [hpow]
      _ = B ^ 2 := by dsimp [B]; ring
  have hsqrt : Real.sqrt (T * MS) = B := by
    rw [hinside, Real.sqrt_sq hB]
  have hgap : 0 ≤
      c₁ * (H * T ^ (3 / 4 : ℝ)) - Real.sqrt (T * MS) := by
    have hMain0 : 0 ≤ c₁ * (H * T ^ (3 / 4 : ℝ)) := by positivity
    rw [hsqrt]
    dsimp [B]
    calc
      0 ≤ (1 / 2 : ℝ) * (c₁ * (H * T ^ (3 / 4 : ℝ))) :=
        mul_nonneg (by norm_num) hMain0
      _ = c₁ * (H * T ^ (3 / 4 : ℝ)) -
          c₁ / 2 * (H * T ^ (3 / 4 : ℝ)) := by ring
  have hstrict :=
    MathlibAux.firstMomentGap_sq_le_strictCancellation_measure_mul_absSecondMoment
      (continuous_selbergCompletedMollifiedF (1 / T) X)
      hTpos.le hH.le hMS hS4real hS2MS hAbsInt hS3bound hgap
  rw [hsqrt] at hstrict
  let Q : ℝ := H ^ 2 * T ^ (1 / 2 : ℝ)
  have hQ : 0 < Q := by dsimp [Q]; positivity
  have hgapPower :
      (c₁ * (H * T ^ (3 / 4 : ℝ)) - B) ^ 2 =
        (c₁ ^ 2 / 4 * T) * Q := by
    calc
      (c₁ * (H * T ^ (3 / 4 : ℝ)) - B) ^ 2 =
          c₁ ^ 2 / 4 * (H ^ 2 * (T ^ (3 / 4 : ℝ)) ^ 2) := by
            dsimp [B]
            ring
      _ = (c₁ ^ 2 / 4 * T) * Q := by
        rw [hpow]
        dsimp [Q]
        ring
  rw [hgapPower] at hstrict
  have hcancel : c₁ ^ 2 / 4 * T ≤
      volume.real (Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) * C3 := by
    have hmult : Q * (c₁ ^ 2 / 4 * T) ≤
        Q * (volume.real
          (Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) * C3) := by
      calc
      Q * (c₁ ^ 2 / 4 * T) = (c₁ ^ 2 / 4 * T) * Q := by ring
      _ ≤ volume.real
          (Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) * MA := hstrict
      _ = Q * (volume.real
          (Icc 0 T ∩ MathlibAux.strictCancellationStarts F H) * C3) := by
        dsimp [MA, Q]
        ring
    exact le_of_mul_le_mul_left hmult hQ
  have hkRewrite : κ * T = (c₁ ^ 2 / 4 * T) / C3 := by
    dsimp [κ]
    field_simp [hC3.ne']
  rw [hkRewrite]
  exact (div_le_iff₀ hC3).2 (by simpa only [mul_comm] using hcancel)

end HardyTheorem
