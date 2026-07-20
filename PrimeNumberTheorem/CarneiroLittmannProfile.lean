import PrimeNumberTheorem.MonotoneExtremalKernel
import Mathlib.MeasureTheory.Integral.Bochner.Set

open Complex MeasureTheory Set

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

/-- Once the four remaining integral/Fourier facts are supplied, the concrete
tail profile satisfies the full extremal-kernel certificate.  Nonnegativity and
dilation monotonicity are discharged here from the density formula. -/
theorem carneiroLittmannTailProfile_certificate
    (hdensity : Integrable carneiroLittmannDensity)
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
    exact signedRadialTailProfile_dilation_antitone hdensity
      (fun _ => carneiroLittmannDensity_nonnegative)
      (fun _ => carneiroLittmannDensity_nonpositive) hNew horder t

end DirichletPolynomial
end PrimeNumberTheorem
