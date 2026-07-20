import PrimeNumberTheorem.MonotoneExtremalKernel
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Asymptotics Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The two-sided tail profile associated to a density which is nonnegative on
the positive half-line and nonpositive on the negative half-line.  The factor
`2` matches the normalization of the Carneiro--Littmann majorant error. -/
noncomputable def signedRadialTailProfile (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    2 * ∫ t in Ici x, q t
  else
    2 * ∫ t in Iic x, -q t

theorem signedRadialTailProfile_nonnegative
    {q : ℝ → ℝ}
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) (x : ℝ) :
    0 ≤ signedRadialTailProfile q x := by
  rw [signedRadialTailProfile]
  split_ifs with hx
  · exact mul_nonneg (by norm_num) <|
      setIntegral_nonneg measurableSet_Ici fun t ht => hpos t (hx.trans ht)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    exact mul_nonneg (by norm_num) <|
      setIntegral_nonneg measurableSet_Iic fun t ht =>
        neg_nonneg.mpr (hneg t (ht.trans hx'))

/-- On the nonnegative half-line, moving the lower endpoint to the right can
only decrease the positive tail integral. -/
theorem signedRadialTailProfile_antitoneOn_nonnegative
    {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x) :
    AntitoneOn (signedRadialTailProfile q) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  simp only [signedRadialTailProfile, if_pos hx.le, if_pos hy.le]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hq.integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hpos t (hx.trans_le ht).le
  · exact (Ici_subset_Ici.mpr hxy).eventuallyLE

/-- On the nonpositive half-line, moving the upper endpoint to the right can
only increase the tail integral of the negated density. -/
theorem signedRadialTailProfile_monotoneOn_nonpositive
    {q : ℝ → ℝ} (hq : Integrable q)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) :
    MonotoneOn (signedRadialTailProfile q) (Iio 0) := by
  intro x hx y hy hxy
  change x < 0 at hx
  change y < 0 at hy
  simp only [signedRadialTailProfile, if_neg (not_le_of_gt hx),
    if_neg (not_le_of_gt hy)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hq.neg.integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact neg_nonneg.mpr (hneg t (ht.trans hy.le))
  · exact (Iic_subset_Iic.mpr hxy).eventuallyLE

/-- Positive dilation shrinks the profile pointwise when its scale increases.
This is the exact monotonicity field required by
`MonotoneExtremalKernelCertificate`. -/
theorem signedRadialTailProfile_dilation_antitone
    {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (horder : deltaNew ≤ deltaOld) (t : ℝ) :
    signedRadialTailProfile q (deltaOld * t) ≤
      signedRadialTailProfile q (deltaNew * t) := by
  have hOld : 0 < deltaOld := hNew.trans_le horder
  by_cases ht0 : t = 0
  · subst t
    simp
  by_cases ht : 0 < t
  · exact signedRadialTailProfile_antitoneOn_nonnegative hq hpos
      (mul_pos hNew ht) (mul_pos hOld ht)
      (mul_le_mul_of_nonneg_right horder ht.le)
  · have ht' : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
    exact signedRadialTailProfile_monotoneOn_nonpositive hq hneg
      (mul_neg_of_pos_of_neg hOld ht')
      (mul_neg_of_pos_of_neg hNew ht')
      (mul_le_mul_of_nonpos_right horder ht'.le)

/-- The density appearing in the integral formula for the monotone
Carneiro--Littmann majorant of the sign function.  At the removable points
Lean's division convention assigns zero; changing finitely many values does
not affect the intended Lebesgue integrals. -/
noncomputable def carneiroLittmannDensity (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) ^ 2 /
    (Real.pi ^ 2 * x * (x + 1) ^ 2)

theorem carneiroLittmannDensity_nonnegative
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ carneiroLittmannDensity x := by
  unfold carneiroLittmannDensity
  apply div_nonneg (sq_nonneg _)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hx) (sq_nonneg _)

theorem carneiroLittmannDensity_nonpositive
    {x : ℝ} (hx : x ≤ 0) :
    carneiroLittmannDensity x ≤ 0 := by
  unfold carneiroLittmannDensity
  apply div_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hx) (sq_nonneg _)

/-- The density written using the removable singularity of `sin (pi * x)` at
zero.  This identity is also valid at `x = -1` because both sides use Lean's
division-by-zero convention there. -/
theorem carneiroLittmannDensity_eq_sinc_zero (x : ℝ) :
    carneiroLittmannDensity x =
      x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2 := by
  by_cases hx0 : x = 0
  · simp [hx0, carneiroLittmannDensity]
  by_cases hx1 : x + 1 = 0
  · have hx : x = -1 := by linarith
    subst x
    simp [carneiroLittmannDensity, Real.sin_neg]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0)]
  unfold carneiroLittmannDensity
  field_simp [Real.pi_ne_zero, hx0, hx1]

/-- The density written using the removable singularity at `x = -1`.  The
formula is valid away from that one point, including at `x = 0`. -/
theorem carneiroLittmannDensity_eq_sinc_neg_one
    {x : ℝ} (hx : x ≠ -1) :
    carneiroLittmannDensity x =
      Real.sinc (Real.pi * (x + 1)) ^ 2 / x := by
  by_cases hx0 : x = 0
  · simp [hx0, carneiroLittmannDensity]
  have hx1 : x + 1 ≠ 0 := by
    intro hx1
    apply hx
    linarith
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx1)]
  have hsin : Real.sin (Real.pi * (x + 1)) = -Real.sin (Real.pi * x) := by
    rw [mul_add, mul_one, Real.sin_add_pi]
  rw [hsin]
  unfold carneiroLittmannDensity
  field_simp [Real.pi_ne_zero, hx0, hx1]

/-- A continuous representative of `carneiroLittmannDensity`.  The left-hand
formula removes the singularity at `-1`; the right-hand formula removes the
singularity at `0`. -/
noncomputable def carneiroLittmannRegularizedDensity (x : ℝ) : ℝ :=
  if x ≤ -(1 / 2 : ℝ) then
    Real.sinc (Real.pi * (x + 1)) ^ 2 / x
  else
    x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2

theorem continuous_carneiroLittmannRegularizedDensity :
    Continuous carneiroLittmannRegularizedDensity := by
  have hleft : ContinuousOn
      (fun x : ℝ => Real.sinc (Real.pi * (x + 1)) ^ 2 / x)
      (Iic (-(1 / 2 : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      change x ≤ -(1 / 2 : ℝ) at hx
      linarith
  have hright : ContinuousOn
      (fun x : ℝ => x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2)
      (Ici (-(1 / 2 : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      change -(1 / 2 : ℝ) ≤ x at hx
      have : x + 1 ≠ 0 := by linarith
      exact pow_ne_zero 2 this
  change Continuous (fun x : ℝ =>
    if x ≤ -(1 / 2 : ℝ) then
      Real.sinc (Real.pi * (x + 1)) ^ 2 / x
    else
      x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2)
  apply continuous_if_le continuous_id continuous_const hleft hright
  intro x hx
  change x = -(1 / 2 : ℝ) at hx
  subst x
  rw [← carneiroLittmannDensity_eq_sinc_neg_one (by norm_num),
    ← carneiroLittmannDensity_eq_sinc_zero]

theorem carneiroLittmannDensity_ae_eq_regularized :
    carneiroLittmannDensity =ᵐ[volume]
      carneiroLittmannRegularizedDensity := by
  have hne : ∀ᵐ x ∂volume, x ≠ (-1 : ℝ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx
  rw [carneiroLittmannRegularizedDensity]
  split_ifs
  · exact carneiroLittmannDensity_eq_sinc_neg_one hx
  · exact carneiroLittmannDensity_eq_sinc_zero x

theorem locallyIntegrable_carneiroLittmannDensity :
    LocallyIntegrable carneiroLittmannDensity :=
  continuous_carneiroLittmannRegularizedDensity.locallyIntegrable.congr
    carneiroLittmannDensity_ae_eq_regularized.symm

private theorem one_add_sq_le_density_denominator_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    1 + x ^ 2 ≤ Real.pi ^ 2 * x * (x + 1) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hcubic : 2 * x ^ 2 ≤ x * x ^ 2 :=
    mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  have hpoly : 1 + x ^ 2 ≤ x * (x + 1) ^ 2 := by
    nlinarith [sq_nonneg x]
  apply hpoly.trans
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hpi (mul_nonneg hx0 (sq_nonneg (x + 1)))

private theorem one_add_sq_le_four_mul_neg_density_denominator_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    1 + x ^ 2 ≤ 4 * (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
  let y := -x
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hym1 : 0 ≤ y - 1 := by linarith
  have hhalf : y / 2 ≤ y - 1 := by linarith
  have hsq : (y / 2) ^ 2 ≤ (y - 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg (by positivity : 0 ≤ y - 1) (by positivity : 0 ≤ y / 2))]
  have hmul := mul_le_mul_of_nonneg_left hsq hy0
  have hcubic : 2 * y ^ 2 ≤ y * y ^ 2 :=
    mul_le_mul_of_nonneg_right hy (sq_nonneg y)
  have hone : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hpoly : 1 + y ^ 2 ≤ 4 * y * (y - 1) ^ 2 := by
    nlinarith
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hden : 4 * y * (y - 1) ^ 2 ≤
      4 * (Real.pi ^ 2 * y * (y - 1) ^ 2) := by
    nlinarith [mul_nonneg hy0 (sq_nonneg (y - 1)),
      mul_le_mul_of_nonneg_right hpi (mul_nonneg hy0 (sq_nonneg (y - 1)))]
  dsimp [y] at hpoly hden ⊢
  nlinarith

theorem carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    ‖carneiroLittmannDensity x‖ ≤ ‖(1 + x ^ 2)⁻¹‖ := by
  have hx0 : 0 ≤ x := by linarith
  have hden : 0 < Real.pi ^ 2 * x * (x + 1) ^ 2 := by positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (carneiroLittmannDensity_nonnegative hx0),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hone)]
  unfold carneiroLittmannDensity
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ (1 + x ^ 2)⁻¹ * (Real.pi ^ 2 * x * (x + 1) ^ 2) := by
      have h := one_add_sq_le_density_denominator_of_two_le hx
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hone).2 (by simpa using h)

theorem carneiroLittmannDensity_norm_le_four_inv_one_add_sq_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    ‖carneiroLittmannDensity x‖ ≤ 4 * ‖(1 + x ^ 2)⁻¹‖ := by
  have hx0 : x ≤ 0 := by linarith
  have hden : 0 < Real.pi ^ 2 * (-x) * (x + 1) ^ 2 := by
    have hxneg : 0 < -x := by linarith
    have hx1 : x + 1 ≠ 0 := by linarith
    positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonpos (carneiroLittmannDensity_nonpositive hx0),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hone)]
  have hdensity : -carneiroLittmannDensity x =
      Real.sin (Real.pi * x) ^ 2 /
        (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
    have hxne : x ≠ 0 := by linarith
    have hx1 : x + 1 ≠ 0 := by linarith
    unfold carneiroLittmannDensity
    field_simp [Real.pi_ne_zero, hxne, hx1]
  rw [hdensity]
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ 4 * (1 + x ^ 2)⁻¹ *
        (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
      have h := one_add_sq_le_four_mul_neg_density_denominator_of_le_neg_two hx
      have hdiv : 1 ≤
          (4 * (Real.pi ^ 2 * (-x) * (x + 1) ^ 2)) / (1 + x ^ 2) :=
        (le_div_iff₀ hone).2 (by simpa using h)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

theorem carneiroLittmannDensity_isBigO_atTop :
    carneiroLittmannDensity =O[atTop]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ici_mem_atTop (2 : ℝ)] with x hx
  simpa using carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le hx

theorem carneiroLittmannDensity_isBigO_atBot :
    carneiroLittmannDensity =O[atBot]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 4
  filter_upwards [Iic_mem_atBot (-2 : ℝ)] with x hx
  exact carneiroLittmannDensity_norm_le_four_inv_one_add_sq_of_le_neg_two hx

theorem integrable_carneiroLittmannDensity :
    Integrable carneiroLittmannDensity :=
  locallyIntegrable_carneiroLittmannDensity.integrable_of_isBigO_atBot_atTop
    carneiroLittmannDensity_isBigO_atBot
    (integrable_inv_one_add_sq.integrableAtFilter atBot)
    carneiroLittmannDensity_isBigO_atTop
    (integrable_inv_one_add_sq.integrableAtFilter atTop)

/-- The direct two-sided tail-integral candidate for `M - sgn`, where `M` is
the monotone Carneiro--Littmann majorant.  At the origin it uses the right-tail
normalization; this possible one-point difference is immaterial to the
Lebesgue integral and Fourier identities. -/
noncomputable def carneiroLittmannTailProfile (x : ℝ) : ℝ :=
  signedRadialTailProfile carneiroLittmannDensity x

theorem carneiroLittmannTailProfile_nonnegative (x : ℝ) :
    0 ≤ carneiroLittmannTailProfile x := by
  exact signedRadialTailProfile_nonnegative
    (fun _ => carneiroLittmannDensity_nonnegative)
    (fun _ => carneiroLittmannDensity_nonpositive) x

/-- Once the three remaining profile integral/Fourier facts are supplied, the concrete
tail profile satisfies the full extremal-kernel certificate.  Nonnegativity and
dilation monotonicity are discharged here from the now-proved density
integrability and sign formulas. -/
theorem carneiroLittmannTailProfile_certificate
    (hprofile : Integrable carneiroLittmannTailProfile)
    (hmass : ∫ x, carneiroLittmannTailProfile x = 2)
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel carneiroLittmannTailProfile xi =
        (-2 * Complex.I) / xi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile where
  integrable := hprofile
  nonnegative := carneiroLittmannTailProfile_nonnegative
  fourier_zero := by
    rw [fourierKernel_zero, hmass]
    norm_num
  fourier_tail := htail
  dilation_antitone := by
    intro deltaNew deltaOld hNew horder t
    exact signedRadialTailProfile_dilation_antitone
      integrable_carneiroLittmannDensity
      (fun _ => carneiroLittmannDensity_nonnegative)
      (fun _ => carneiroLittmannDensity_nonpositive) hNew horder t

end DirichletPolynomial
end PrimeNumberTheorem
