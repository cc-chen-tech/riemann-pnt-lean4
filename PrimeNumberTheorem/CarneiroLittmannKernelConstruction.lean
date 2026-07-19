import PrimeNumberTheorem.TriangleFourierKernel

open MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- On the negative half-line, the cumulative Carneiro--Littmann derivative
is nonnegative. -/
theorem carneiroLittmannCumulative_nonneg_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    0 ≤ carneiroLittmannCumulative x := by
  unfold carneiroLittmannCumulative
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
  rcases lt_or_eq_of_le (hu.trans hx) with hu0 | rfl
  · exact carneiroLittmannDerivative_nonneg_of_neg hu0
  · simp

/-- On the positive half-line, the cumulative derivative stays above its
unit total mass. -/
theorem one_le_carneiroLittmannCumulative_of_nonneg {x : ℝ} (hx : 0 ≤ x) :
    1 ≤ carneiroLittmannCumulative x := by
  have hsplit :
      (∫ u in Set.Iic x, carneiroLittmannDerivative u) +
          (∫ u in (Set.Iic x)ᶜ, carneiroLittmannDerivative u) =
        ∫ u, carneiroLittmannDerivative u :=
    integral_add_compl (s := Set.Iic x) measurableSet_Iic
      integrable_carneiroLittmannDerivative
  have htail :
      (∫ u in (Set.Iic x)ᶜ, carneiroLittmannDerivative u) ≤ 0 := by
    apply integral_nonpos_of_ae
    filter_upwards [ae_restrict_mem measurableSet_Iic.compl] with u hu
    have hxu : x < u := by simpa only [compl_Iic, Set.mem_Ioi] using hu
    exact carneiroLittmannDerivative_nonpos_of_pos (hx.trans_lt hxu)
  rw [integral_carneiroLittmannDerivative_eq_one] at hsplit
  unfold carneiroLittmannCumulative
  linarith

/-- The error between the cumulative extremal function and the Heaviside
step, with the value at zero taken from the negative side. -/
noncomputable def carneiroLittmannKernelError (x : ℝ) : ℝ :=
  if x ≤ 0 then carneiroLittmannCumulative x
  else carneiroLittmannCumulative x - 1

theorem carneiroLittmannKernelError_nonneg (x : ℝ) :
    0 ≤ carneiroLittmannKernelError x := by
  by_cases hx : x ≤ 0
  · rw [carneiroLittmannKernelError, if_pos hx]
    exact carneiroLittmannCumulative_nonneg_of_nonpos hx
  · rw [carneiroLittmannKernelError, if_neg hx]
    exact sub_nonneg.mpr
      (one_le_carneiroLittmannCumulative_of_nonneg (le_of_not_ge hx))

/-- Positive dilation moves the Heaviside error away from its peak at zero,
so the kernel decreases as the dilation scale grows. -/
theorem carneiroLittmannKernelError_dilation_antitone
    {deltaSmall deltaLarge : ℝ}
    (hsmall : 0 < deltaSmall) (hle : deltaSmall ≤ deltaLarge) (t : ℝ) :
    carneiroLittmannKernelError (deltaLarge * t) ≤
      carneiroLittmannKernelError (deltaSmall * t) := by
  have hlarge : 0 < deltaLarge := hsmall.trans_le hle
  rcases lt_trichotomy t 0 with ht | rfl | ht
  · have hlargeNonpos : deltaLarge * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hlarge.le ht.le
    have hsmallNonpos : deltaSmall * t ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hsmall.le ht.le
    simp only [carneiroLittmannKernelError, if_pos hlargeNonpos,
      if_pos hsmallNonpos]
    exact monotoneOn_carneiroLittmannCumulative_Iic hlargeNonpos hsmallNonpos
      (mul_le_mul_of_nonpos_right hle ht.le)
  · simp [carneiroLittmannKernelError]
  · have hlargePos : 0 < deltaLarge * t := mul_pos hlarge ht
    have hsmallPos : 0 < deltaSmall * t := mul_pos hsmall ht
    simp only [carneiroLittmannKernelError, if_neg (not_le.mpr hlargePos),
      if_neg (not_le.mpr hsmallPos)]
    exact sub_le_sub_right
      (antitoneOn_carneiroLittmannCumulative_Ici hsmallPos.le hlargePos.le
        (mul_le_mul_of_nonneg_right hle ht.le)) 1

end DirichletPolynomial
end PrimeNumberTheorem
