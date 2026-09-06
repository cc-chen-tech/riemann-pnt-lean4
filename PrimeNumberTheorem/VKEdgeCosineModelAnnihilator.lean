import PrimeNumberTheorem.VKEdgeResidualAmplification

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- The symmetric three-point detector with prescribed killed frequency. -/
def symmetricFrequencyAnnihilator
    (h gamma : ℝ) (f : ℝ → ℝ) (y : ℝ) : ℝ :=
  f (y + h) - 2 * Real.cos (gamma * h) * f y + f (y - h)

/-- A cosine of frequency `lambda` is an eigenfunction of the symmetric
detector, with the displayed exact multiplier. -/
theorem symmetricFrequencyAnnihilator_cosinePairModel
    (h gamma m lambda phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m lambda phase) y =
      2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) *
        cosinePairModel m lambda phase y := by
  have hplus :
      Real.cos (lambda * (y + h) - phase) =
        Real.cos (lambda * y - phase) * Real.cos (lambda * h) -
          Real.sin (lambda * y - phase) * Real.sin (lambda * h) := by
    rw [show lambda * (y + h) - phase =
      (lambda * y - phase) + lambda * h by ring]
    exact Real.cos_add _ _
  have hminus :
      Real.cos (lambda * (y - h) - phase) =
        Real.cos (lambda * y - phase) * Real.cos (lambda * h) +
          Real.sin (lambda * y - phase) * Real.sin (lambda * h) := by
    rw [show lambda * (y - h) - phase =
      (lambda * y - phase) - lambda * h by ring]
    exact Real.cos_sub _ _
  simp only [symmetricFrequencyAnnihilator, cosinePairModel]
  rw [hplus, hminus]
  ring

/-- The detector annihilates the selected cosine-pair model pointwise. -/
theorem symmetricFrequencyAnnihilator_cosineModelPair_eq_zero
    (h gamma m phase y : ℝ) :
    symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m gamma phase) y = 0 := by
  rw [symmetricFrequencyAnnihilator_cosinePairModel]
  ring

private theorem symmetricFrequencyAnnihilator_sub
    (h gamma : ℝ) (f p : ℝ → ℝ) (y : ℝ) :
    symmetricFrequencyAnnihilator h gamma (fun z => f z - p z) y =
      symmetricFrequencyAnnihilator h gamma f y -
        symmetricFrequencyAnnihilator h gamma p y := by
  simp only [symmetricFrequencyAnnihilator]
  ring

/--
The normalized PNT error after applying a detector tuned to `rho.im`.
This is an exact operation on the arithmetic error; it does not identify the
subtracted cosine model with a zeta explicit-formula term.
-/
def annihilatedNormalizedPsiError
    (rho : ℂ) (h y : ℝ) : ℝ :=
  symmetricFrequencyAnnihilator h rho.im (normalizedPsiError rho) y

/--
Applying the detector to the full normalized error is exactly the same as
applying it to the formal psi-minus-cosine-model residual.
-/
theorem annihilatedNormalizedPsiError_eq_modelResidual
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      symmetricFrequencyAnnihilator h rho.im
        (normalizedPsiModelResidual rho) y := by
  have htarget :
      symmetricFrequencyAnnihilator h rho.im
          (normalizedCosineModelPair rho) y = 0 := by
    change symmetricFrequencyAnnihilator h rho.im
        (fun z : ℝ => normalizedCosineModelPair rho z) y = 0
    simpa only [normalizedCosineModelPair] using
      symmetricFrequencyAnnihilator_cosineModelPair_eq_zero
        h rho.im (analyticOrderNatAt riemannZeta rho : ℝ) rho.arg y
  unfold annihilatedNormalizedPsiError normalizedPsiModelResidual
  rw [symmetricFrequencyAnnihilator_sub, htarget, sub_zero]

/--
Exact arithmetic form of the frequency-tuned detector: a signed three-scale
correlation of the classical PNT error.
-/
theorem annihilatedNormalizedPsiError_eq_threeScale
    (rho : ℂ) (h y : ℝ) :
    annihilatedNormalizedPsiError rho h y =
      ‖rho‖ * Real.exp (-rho.re * y) *
        (Real.exp (-rho.re * h) *
            (chebyshevPsi (Real.exp (y + h)) - Real.exp (y + h)) -
          2 * Real.cos (rho.im * h) *
            (chebyshevPsi (Real.exp y) - Real.exp y) +
          Real.exp (rho.re * h) *
            (chebyshevPsi (Real.exp (y - h)) - Real.exp (y - h))) := by
  have hplus :
      Real.exp (-rho.re * (y + h)) =
        Real.exp (-rho.re * y) * Real.exp (-rho.re * h) := by
    rw [show -rho.re * (y + h) = -rho.re * y + -rho.re * h by ring,
      Real.exp_add]
  have hminus :
      Real.exp (-rho.re * (y - h)) =
        Real.exp (-rho.re * y) * Real.exp (rho.re * h) := by
    rw [show -rho.re * (y - h) = -rho.re * y + rho.re * h by ring,
      Real.exp_add]
  simp only [annihilatedNormalizedPsiError, symmetricFrequencyAnnihilator,
    normalizedPsiError, hplus, hminus]
  ring

/-- The three-point detector is bounded in `L²` by its three input samples. -/
theorem sq_symmetricFrequencyAnnihilator_le
    (f : ℝ → ℝ) (h gamma y : ℝ) :
    symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤
      12 * (f (y + h) ^ 2 + f y ^ 2 + f (y - h) ^ 2) := by
  have hcos :
      Real.cos (gamma * h) ^ 2 ≤ 1 := by
    have hprod :
        0 ≤ (1 - Real.cos (gamma * h)) *
          (1 + Real.cos (gamma * h)) :=
      mul_nonneg
        (sub_nonneg.mpr (Real.cos_le_one _))
        (by linarith [Real.neg_one_le_cos (gamma * h)])
    nlinarith
  have hthree :
      (f (y + h) -
          2 * Real.cos (gamma * h) * f y +
          f (y - h)) ^ 2 ≤
        3 * (f (y + h) ^ 2 +
          (-2 * Real.cos (gamma * h) * f y) ^ 2 +
          f (y - h) ^ 2) := by
    nlinarith [
      sq_nonneg (f (y + h) - (-2 * Real.cos (gamma * h) * f y)),
      sq_nonneg (f (y + h) - f (y - h)),
      sq_nonneg ((-2 * Real.cos (gamma * h) * f y) - f (y - h))]
  have hmiddle :
      (-2 * Real.cos (gamma * h) * f y) ^ 2 ≤
        4 * f y ^ 2 := by
    nlinarith [sq_nonneg (f y)]
  unfold symmetricFrequencyAnnihilator
  nlinarith [sq_nonneg (f (y + h)), sq_nonneg (f y),
    sq_nonneg (f (y - h))]

/-- Integrating the pointwise detector estimate costs at most a factor `36`
when each of the three shifted input energies is at most `E`. -/
theorem integral_sq_symmetricFrequencyAnnihilator_le_of_shifted
    {f : ℝ → ℝ} {s : Set ℝ} {h gamma E : ℝ}
    (hplusInt : IntegrableOn (fun y => f (y + h) ^ 2) s)
    (hzeroInt : IntegrableOn (fun y => f y ^ 2) s)
    (hminusInt : IntegrableOn (fun y => f (y - h) ^ 2) s)
    (hdetInt :
      IntegrableOn
        (fun y => symmetricFrequencyAnnihilator h gamma f y ^ 2) s)
    (hplus : ∫ y in s, f (y + h) ^ 2 ≤ E)
    (hzero : ∫ y in s, f y ^ 2 ≤ E)
    (hminus : ∫ y in s, f (y - h) ^ 2 ≤ E) :
    ∫ y in s, symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤ 36 * E := by
  have hmajorInt :
      IntegrableOn
        (fun y => 12 *
          (f (y + h) ^ 2 + f y ^ 2 + f (y - h) ^ 2)) s :=
    ((hplusInt.add hzeroInt).add hminusInt).const_mul 12
  have hmono :
      (∫ y in s, symmetricFrequencyAnnihilator h gamma f y ^ 2) ≤
        ∫ y in s, 12 *
          (f (y + h) ^ 2 + f y ^ 2 + f (y - h) ^ 2) := by
    apply integral_mono_ae hdetInt hmajorInt
    exact Filter.Eventually.of_forall fun y =>
      sq_symmetricFrequencyAnnihilator_le f h gamma y
  rw [integral_const_mul, integral_add, integral_add] at hmono
  · nlinarith
  · exact hplusInt
  · exact hzeroInt
  · exact hplusInt.add hzeroInt
  · exact hminusInt

/--
The same stability estimate for the frequency-tuned normalized PNT error,
expressed through shifted energies of the formal model residual.
-/
theorem integral_annihilatedNormalizedPsiError_sq_le_of_modelResidual_shifts
    {rho : ℂ} {s : Set ℝ} {h E : ℝ}
    (hplusInt :
      IntegrableOn
        (fun y => normalizedPsiModelResidual rho (y + h) ^ 2) s)
    (hzeroInt :
      IntegrableOn (fun y => normalizedPsiModelResidual rho y ^ 2) s)
    (hminusInt :
      IntegrableOn
        (fun y => normalizedPsiModelResidual rho (y - h) ^ 2) s)
    (hdetInt :
      IntegrableOn
        (fun y => annihilatedNormalizedPsiError rho h y ^ 2) s)
    (hplus :
      ∫ y in s, normalizedPsiModelResidual rho (y + h) ^ 2 ≤ E)
    (hzero :
      ∫ y in s, normalizedPsiModelResidual rho y ^ 2 ≤ E)
    (hminus :
      ∫ y in s, normalizedPsiModelResidual rho (y - h) ^ 2 ≤ E) :
    ∫ y in s, annihilatedNormalizedPsiError rho h y ^ 2 ≤ 36 * E := by
  simp_rw [annihilatedNormalizedPsiError_eq_modelResidual] at hdetInt ⊢
  exact integral_sq_symmetricFrequencyAnnihilator_le_of_shifted
    hplusInt hzeroInt hminusInt hdetInt hplus hzero hminus

/--
Positive detector energy on an inner interval forces the original signal to
have a pointwise square lower bound on the interval expanded by `|h|`.
-/
theorem exists_mem_expandedInterval_sq_gt_of_detector_energy_pos
    {f : ℝ → ℝ} {a b h gamma : ℝ}
    (hab : a < b)
    (hdetInt :
      IntegrableOn
        (fun y => symmetricFrequencyAnnihilator h gamma f y ^ 2)
        (Icc a b))
    (henergy :
      0 <
        ∫ y in Icc a b,
          symmetricFrequencyAnnihilator h gamma f y ^ 2) :
    ∃ z ∈ Icc (a - |h|) (b + |h|),
      (∫ y in Icc a b,
          symmetricFrequencyAnnihilator h gamma f y ^ 2) /
          (72 * (b - a)) <
        f z ^ 2 := by
  let energy : ℝ :=
    ∫ y in Icc a b,
      symmetricFrequencyAnnihilator h gamma f y ^ 2
  let threshold : ℝ := energy / (72 * (b - a))
  have hlength : 0 < b - a := sub_pos.mpr hab
  by_contra hexists
  push Not at hexists
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      symmetricFrequencyAnnihilator h gamma f y ^ 2 ≤
        36 * threshold := by
    have hyPlus : y + h ∈ Icc (a - |h|) (b + |h|) := by
      constructor
      · linarith [hy.1, neg_abs_le h]
      · linarith [hy.2, le_abs_self h]
    have hyZero : y ∈ Icc (a - |h|) (b + |h|) := by
      constructor
      · linarith [hy.1, abs_nonneg h]
      · linarith [hy.2, abs_nonneg h]
    have hyMinus : y - h ∈ Icc (a - |h|) (b + |h|) := by
      constructor
      · linarith [hy.1, le_abs_self h]
      · linarith [hy.2, neg_abs_le h]
    have hplus := hexists (y + h) hyPlus
    have hzero := hexists y hyZero
    have hminus := hexists (y - h) hyMinus
    have hdetector :=
      sq_symmetricFrequencyAnnihilator_le f h gamma y
    nlinarith
  have hmajorInt :
      IntegrableOn (fun _y : ℝ => 36 * threshold) (Icc a b) :=
    integrableOn_const (μ := volume) (s := Icc a b)
      measure_Icc_lt_top.ne
  have hmono :
      (∫ y in Icc a b,
          symmetricFrequencyAnnihilator h gamma f y ^ 2) ≤
        ∫ _y in Icc a b, 36 * threshold := by
    apply integral_mono_ae hdetInt hmajorInt
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint y hy
  have hconstant :
      (∫ _y in Icc a b, 36 * threshold) =
        36 * threshold * (b - a) := by
    rw [integral_const]
    change
      (volume.restrict (Icc a b)).real Set.univ *
          (36 * threshold) =
        36 * threshold * (b - a)
    rw [Measure.real, Measure.restrict_apply_univ,
      Real.volume_Icc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab.le)]
    ring
  have hhalf :
      36 * threshold * (b - a) = energy / 2 := by
    dsimp only [threshold]
    field_simp [hlength.ne']
    <;> ring
  have hcontradiction : energy ≤ energy / 2 := by
    calc
      energy =
          ∫ y in Icc a b,
            symmetricFrequencyAnnihilator h gamma f y ^ 2 := rfl
      _ ≤ ∫ _y in Icc a b, 36 * threshold := hmono
      _ = 36 * threshold * (b - a) := hconstant
      _ = energy / 2 := hhalf
  dsimp only [energy] at hcontradiction
  nlinarith

/--
Specialization of the inner-to-outer pointwise transfer to the formal
psi-minus-cosine-model residual. It does not identify that residual with the
contribution of other zeta zeros or contour terms.
-/
theorem exists_mem_expandedInterval_normalizedPsiModelResidual_sq_gt
    {rho : ℂ} {a b h : ℝ}
    (hab : a < b)
    (hdetInt :
      IntegrableOn
        (fun y => annihilatedNormalizedPsiError rho h y ^ 2)
        (Icc a b))
    (henergy :
      0 <
        ∫ y in Icc a b,
          annihilatedNormalizedPsiError rho h y ^ 2) :
    ∃ z ∈ Icc (a - |h|) (b + |h|),
      (∫ y in Icc a b,
          annihilatedNormalizedPsiError rho h y ^ 2) /
          (72 * (b - a)) <
        normalizedPsiModelResidual rho z ^ 2 := by
  have hdetIntModel :
      IntegrableOn
        (fun y =>
          symmetricFrequencyAnnihilator h rho.im
            (normalizedPsiModelResidual rho) y ^ 2)
        (Icc a b) := by
    simpa only [annihilatedNormalizedPsiError_eq_modelResidual] using hdetInt
  have henergyModel :
      0 <
        ∫ y in Icc a b,
          symmetricFrequencyAnnihilator h rho.im
            (normalizedPsiModelResidual rho) y ^ 2 := by
    simpa only [annihilatedNormalizedPsiError_eq_modelResidual] using henergy
  simpa only [annihilatedNormalizedPsiError_eq_modelResidual] using
    exists_mem_expandedInterval_sq_gt_of_detector_energy_pos
      hab hdetIntModel henergyModel

/--
The pure cosine model alone cannot supply a positive lower bound after the
detector has annihilated it.
-/
theorem no_positive_lower_bound_on_pure_cosine_model
    {h gamma m phase C a b : ℝ}
    (hC : 0 < C) (hab : a < b) :
    ¬ C * (b - a) ≤
      ∫ y in Set.Icc a b,
        symmetricFrequencyAnnihilator h gamma
          (cosinePairModel m gamma phase) y ^ 2 := by
  have hzero :
      (∫ y in Set.Icc a b,
        symmetricFrequencyAnnihilator h gamma
          (cosinePairModel m gamma phase) y ^ 2) = 0 := by
    simp_rw [symmetricFrequencyAnnihilator_cosineModelPair_eq_zero]
    simp
  rw [hzero]
  exact not_le_of_gt (mul_pos hC (sub_pos.mpr hab))

/-- At a point where the cosine model is nonzero, a second frequency is
annihilated exactly when its detector multiplier collides with the selected
frequency multiplier. -/
theorem symmetricFrequencyAnnihilator_cosinePairModel_eq_zero_iff
    {h gamma m lambda phase y : ℝ}
    (hm : m ≠ 0)
    (hy : Real.cos (lambda * y - phase) ≠ 0) :
    symmetricFrequencyAnnihilator h gamma
        (cosinePairModel m lambda phase) y = 0 ↔
      Real.cos (lambda * h) = Real.cos (gamma * h) := by
  rw [symmetricFrequencyAnnihilator_cosinePairModel]
  have hpair :
      cosinePairModel m lambda phase y ≠ 0 := by
    unfold cosinePairModel
    exact mul_ne_zero (mul_ne_zero (by norm_num) hm) hy
  constructor
  · intro hzero
    have hcoefficient :
        2 * (Real.cos (lambda * h) - Real.cos (gamma * h)) = 0 :=
      (mul_eq_zero.mp hzero).resolve_right hpair
    have hdifference :
        Real.cos (lambda * h) - Real.cos (gamma * h) = 0 :=
      (mul_eq_zero.mp hcoefficient).resolve_left (by norm_num)
    linarith
  · intro hcollision
    rw [hcollision]
    ring

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
