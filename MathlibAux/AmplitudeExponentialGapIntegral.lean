import MathlibAux.SlidingExponentialCoefficientBound

/-!
# Oscillatory gap bounds with a varying amplitude

Integration by parts gives a reciprocal-frequency bound for one exponential
mode multiplied by an amplitude of bounded total variation.  Summing the
one-mode estimate yields an explicit gap-sum bound for arbitrary finite
frequency sets.
-/

open Complex MeasureTheory Set

namespace MathlibAux

/-- A finite off-diagonal exponential form with arbitrary real frequencies. -/
noncomputable def exponentialOffDiagonalForm
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (left right : ι → ℂ) (freq : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ i ∈ s, ∑ j ∈ s,
    if i = j then 0
    else left i * right j *
      Complex.exp (I * ((freq i - freq j) * t))

/-- A bounded-variation amplitude costs only its endpoint mass and total
variation in the standard reciprocal-frequency estimate. -/
theorem norm_integral_amplitude_mul_cexp_linear_le
    {A A' : ℝ → ℂ} {a b K V lambda : ℝ}
    (hab : a ≤ b) (hlambda : lambda ≠ 0)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hAend : ‖A a‖ ≤ K ∧ ‖A b‖ ≤ K)
    (hA'int : IntervalIntegrable A' volume a b)
    (hvariation : (∫ x in a..b, ‖A' x‖) ≤ V) :
    ‖∫ t in a..b, A t * Complex.exp (I * (lambda * t))‖ ≤
      (2 * K + V) / |lambda| := by
  let c : ℂ := I * (lambda : ℂ)
  let E : ℝ → ℂ := fun t => Complex.exp (c * t) / c
  let E' : ℝ → ℂ := fun t => Complex.exp (c * t)
  have hlambdaAbs : 0 < |lambda| := abs_pos.mpr hlambda
  have hden : ‖c‖ = |lambda| := by
    dsimp only [c]
    rw [norm_mul, norm_I, norm_real, Real.norm_eq_abs, one_mul]
  have hEderiv : ∀ x ∈ Set.uIcc a b, HasDerivAt E (E' x) x := by
    intro x hx
    have harg : HasDerivAt (fun y : ℝ => c * y) c x := by
      simpa using Complex.ofRealCLM.hasDerivAt.const_mul c
    have hexp := harg.cexp
    have hdenNe : c ≠ 0 := by
      dsimp only [c]
      exact
      mul_ne_zero I_ne_zero (ofReal_ne_zero.mpr hlambda)
    simpa only [E, E', mul_div_cancel_right₀ _ hdenNe] using
      hexp.div_const c
  have hE'int : IntervalIntegrable E' volume a b := by
    apply Continuous.intervalIntegrable
    dsimp only [E']
    fun_prop
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hA hEderiv hA'int hE'int
  have hEbound (x : ℝ) : ‖E x‖ = 1 / |lambda| := by
    dsimp only [E]
    rw [norm_div, hden, Complex.norm_exp]
    simp [c]
  have hend :
      ‖A b * E b - A a * E a‖ ≤ 2 * K / |lambda| := by
    calc
      ‖A b * E b - A a * E a‖ ≤
          ‖A b * E b‖ + ‖A a * E a‖ := norm_sub_le _ _
      _ = ‖A b‖ * (1 / |lambda|) +
          ‖A a‖ * (1 / |lambda|) := by
        rw [norm_mul, norm_mul, hEbound, hEbound]
      _ ≤ K * (1 / |lambda|) + K * (1 / |lambda|) := by
        exact add_le_add
          (mul_le_mul_of_nonneg_right hAend.2
            (one_div_nonneg.mpr hlambdaAbs.le))
          (mul_le_mul_of_nonneg_right hAend.1
            (one_div_nonneg.mpr hlambdaAbs.le))
      _ = 2 * K / |lambda| := by ring
  have hrem :
      ‖∫ x in a..b, A' x * E x‖ ≤ V / |lambda| := by
    have hmajorInt :
        IntervalIntegrable (fun x => (1 / |lambda|) * ‖A' x‖)
          volume a b :=
      (hA'int.norm).const_mul (1 / |lambda|)
    have hnorm := intervalIntegral.norm_integral_le_of_norm_le
      (f := fun x : ℝ => A' x * E x)
      (g := fun x : ℝ => (1 / |lambda|) * ‖A' x‖) hab
      (by
        filter_upwards with x
        intro hx
        rw [norm_mul, hEbound x]
        exact le_of_eq (mul_comm ‖A' x‖ (1 / |lambda|)))
      hmajorInt
    calc
      ‖∫ x in a..b, A' x * E x‖ ≤
          ∫ x in a..b, (1 / |lambda|) * ‖A' x‖ := hnorm
      _ = (1 / |lambda|) * ∫ x in a..b, ‖A' x‖ :=
        intervalIntegral.integral_const_mul _ _
      _ ≤ (1 / |lambda|) * V :=
        mul_le_mul_of_nonneg_left hvariation
          (one_div_nonneg.mpr hlambdaAbs.le)
      _ = V / |lambda| := by ring
  have hidentity :
      (∫ x in a..b, A x * E' x) =
        A b * E b - A a * E a - ∫ x in a..b, A' x * E x :=
    hparts
  calc
    ‖∫ t in a..b, A t * Complex.exp (I * (lambda * t))‖ =
        ‖∫ t in a..b, A t * E' t‖ := by
      apply congrArg norm
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only [E', c]
      congr 2
      ring
    _ = ‖A b * E b - A a * E a -
          ∫ x in a..b, A' x * E x‖ := by rw [hidentity]
    _ ≤ ‖A b * E b - A a * E a‖ +
          ‖∫ x in a..b, A' x * E x‖ := norm_sub_le _ _
    _ ≤ 2 * K / |lambda| + V / |lambda| := add_le_add hend hrem
    _ = (2 * K + V) / |lambda| := by ring

/-- Summing the one-mode estimate bounds an arbitrary finite off-diagonal
form by its explicit reciprocal-frequency gap sum. -/
theorem norm_integral_amplitude_mul_exponentialOffDiagonal_le
    {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (left right : ι → ℂ) (freq : ι → ℝ)
    {A A' : ℝ → ℂ} {a b K V : ℝ}
    (hab : a ≤ b)
    (hfreq : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → freq i ≠ freq j)
    (hA : ∀ x ∈ Set.uIcc a b, HasDerivAt A (A' x) x)
    (hAend : ‖A a‖ ≤ K ∧ ‖A b‖ ≤ K)
    (hA'int : IntervalIntegrable A' volume a b)
    (hvariation : (∫ x in a..b, ‖A' x‖) ≤ V) :
    ‖∫ t in a..b,
        A t * exponentialOffDiagonalForm s left right freq t‖ ≤
      ∑ i ∈ s, ∑ j ∈ s,
        if i = j then 0
        else ‖left i‖ * ‖right j‖ *
          ((2 * K + V) / |freq i - freq j|) := by
  have hAcont : ContinuousOn A (Set.uIcc a b) := by
    intro x hx
    exact (hA x hx).continuousAt.continuousWithinAt
  have htermInt (i : ι) (j : ι) :
      IntervalIntegrable
        (fun t : ℝ => A t *
          (if i = j then 0
          else left i * right j *
            Complex.exp (I * ((freq i - freq j) * t))))
        volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply hAcont.mul
    split_ifs <;> fun_prop
  have hsum :
      (∫ t in a..b,
          A t * exponentialOffDiagonalForm s left right freq t) =
        ∑ i ∈ s, ∑ j ∈ s,
          ∫ t in a..b, A t *
            (if i = j then 0
            else left i * right j *
              Complex.exp (I * ((freq i - freq j) * t))) := by
    rw [show (fun t : ℝ =>
        A t * exponentialOffDiagonalForm s left right freq t) =
        fun t : ℝ => ∑ i ∈ s, ∑ j ∈ s,
          A t * (if i = j then 0
          else left i * right j *
            Complex.exp (I * ((freq i - freq j) * t))) by
      funext t
      simp only [exponentialOffDiagonalForm, Finset.mul_sum]]
    rw [intervalIntegral.integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [intervalIntegral.integral_finset_sum]
      intro j hj
      exact htermInt i j
    · intro i hi
      apply ContinuousOn.intervalIntegrable
      apply continuousOn_finset_sum
      intro j hj
      apply hAcont.mul
      split_ifs <;> fun_prop
  rw [hsum]
  calc
    ‖∑ i ∈ s, ∑ j ∈ s,
        ∫ t in a..b, A t *
          (if i = j then 0
          else left i * right j *
            Complex.exp (I * ((freq i - freq j) * t)))‖ ≤
        ∑ i ∈ s, ‖∑ j ∈ s,
          ∫ t in a..b, A t *
            (if i = j then 0
            else left i * right j *
              Complex.exp (I * ((freq i - freq j) * t)))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        ‖∫ t in a..b, A t *
          (if i = j then 0
          else left i * right j *
            Complex.exp (I * ((freq i - freq j) * t)))‖ := by
      apply Finset.sum_le_sum
      intro i hi
      exact norm_sum_le _ _
    _ ≤ ∑ i ∈ s, ∑ j ∈ s,
        if i = j then 0
        else ‖left i‖ * ‖right j‖ *
          ((2 * K + V) / |freq i - freq j|) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Finset.sum_le_sum
      intro j hj
      by_cases hij : i = j
      · simp [hij]
      · simp only [hij, ↓reduceIte]
        rw [show (fun t : ℝ => A t *
            (left i * right j *
              Complex.exp (I * ((freq i - freq j) * t)))) =
            fun t : ℝ => (left i * right j) *
              (A t * Complex.exp (I * ((freq i - freq j) * t))) by
          funext t
          ring]
        have hfactor :
            (∫ t in a..b, (left i * right j) *
              (A t * Complex.exp (I * ((freq i - freq j) * t)))) =
              (left i * right j) *
                ∫ t in a..b,
                  A t * Complex.exp (I * ((freq i - freq j) * t)) :=
          intervalIntegral.integral_const_mul _ _
        rw [hfactor, norm_mul, norm_mul]
        refine mul_le_mul_of_nonneg_left ?_
          (mul_nonneg (norm_nonneg _) (norm_nonneg _))
        have hsingle :=
          norm_integral_amplitude_mul_cexp_linear_le
            hab (sub_ne_zero.mpr (hfreq i hi j hj hij))
            hA hAend hA'int hvariation
        simpa only [ofReal_sub, ofReal_mul, norm_mul] using hsingle
