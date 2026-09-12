import PrimeNumberTheorem.MWKFCubicAFEInfiniteCompletedMoment
import PrimeNumberTheorem.MWKFCubicFinal

open Filter Asymptotics MeasureTheory

namespace PrimeNumberTheorem.MWKFCubic

/-!
# A total exact decomposition of the actual cubic moment

At nonzero height these functions are the principal and nonzero completed
modes at the fixed admissible Mellin line `X = 1`.  The completion depth may
be any finite schedule `J(T)`.  The definitions patch the single point `T = 0`
so that the exact identity is total on `ℝ`; this point does not change either
asymptotic hypothesis at `atTop`.

This module supplies the exact-decomposition input of `MWKFCubicFinal`.  It
does not prove the reciprocal-LCM main-term asymptotic or the cubic Mobius
decorrelation estimate.
-/

/-- The literal moment vanishes at `T = 0`.  Indeed `t / 0 = 0`, while the
support condition on the test weight forces `W 0 = 0`. -/
theorem cubicMollifiedSecondMoment_zero (W : CubicTestWeight) :
    cubicMollifiedSecondMoment W 0 = 0 := by
  have hW0 : W 0 = 0 := by
    by_contra h
    have hmem : (0 : ℝ) ∈ Function.support W := by
      change W 0 ≠ 0
      exact h
    have hIcc := W.support_subset hmem
    norm_num at hIcc
  unfold cubicMollifiedSecondMoment
  have hzero : cubicMomentIntegrand W 0 = fun _t ↦ 0 := by
    funext t
    simp [cubicMomentIntegrand, hW0]
  rw [hzero]
  exact integral_zero ℝ ℝ

/-- The completed principal part for a finite depth schedule and the canonical
admissible Mellin line `X = 1`, extended by zero at `T = 0`. -/
noncomputable def cubicAFECompletionSchedulePrincipalPart
    (W : CubicTestWeight) (J : ℝ → ℕ) (T : ℝ) : ℝ :=
  if T = 0 then 0 else cubicAFECompletedPrincipalPart W T 1 (J T)

/-- The completed nonzero-mode remainder for a finite depth schedule and
`X = 1`.
At `T = 0` it is set to zero, matching `cubicMollifiedSecondMoment_zero`
without identifying the zero-height value with a nonzero-height completed
expression. -/
noncomputable def cubicAFECompletionScheduleRemainder
    (W : CubicTestWeight) (J : ℝ → ℕ) (T : ℝ) : ℝ :=
  if T = 0 then 0
  else cubicAFECompletedRemainder W T 1 (J T)

/-- The scheduled principal part specialized to a constant completion depth. -/
noncomputable def cubicAFEFixedDepthPrincipalPart
    (W : CubicTestWeight) (J : ℕ) : ℝ → ℝ :=
  cubicAFECompletionSchedulePrincipalPart W (fun _T ↦ J)

/-- The scheduled remainder specialized to a constant completion depth. -/
noncomputable def cubicAFEFixedDepthRemainder
    (W : CubicTestWeight) (J : ℕ) : ℝ → ℝ :=
  cubicAFECompletionScheduleRemainder W (fun _T ↦ J)

/-- The literal cubic mollified moment has an exact principal/remainder
decomposition for every real `T` and every finite completion-depth schedule.
For `T ≠ 0` this is the proved completed-mode identity; `T = 0` is handled
by the explicit endpoint patch above. -/
theorem cubicMollifiedSecondMoment_eq_completionSchedule_principal_remainder
    (W : CubicTestWeight) (J : ℝ → ℕ) (T : ℝ) :
    cubicMollifiedSecondMoment W T =
      T * cubicAFECompletionSchedulePrincipalPart W J T +
        cubicAFECompletionScheduleRemainder W J T := by
  by_cases hT : T = 0
  · subst T
    simp [cubicAFECompletionSchedulePrincipalPart,
      cubicAFECompletionScheduleRemainder, cubicMollifiedSecondMoment_zero]
  · simp only [cubicAFECompletionSchedulePrincipalPart,
      cubicAFECompletionScheduleRemainder, hT, if_false]
    exact cubicMollifiedSecondMoment_eq_completed_principal_remainder
      W hT (by norm_num) (J T)

/-- Constant-depth specialization of the total exact decomposition. -/
theorem cubicMollifiedSecondMoment_eq_fixedDepth_principal_remainder
    (W : CubicTestWeight) (J : ℕ) (T : ℝ) :
    cubicMollifiedSecondMoment W T =
      T * cubicAFEFixedDepthPrincipalPart W J T +
        cubicAFEFixedDepthRemainder W J T := by
  exact cubicMollifiedSecondMoment_eq_completionSchedule_principal_remainder
    W (fun _T ↦ J) T

/-- The final asymptotic specialized to a genuine scheduled completed
principal part and nonzero-mode remainder.  No separate exact-decomposition
hypothesis remains; the two displayed little-o estimates are the still-
unproved analytic inputs. -/
theorem cubic_actual_long_mollifier_asymptotic_of_completionSchedule_estimates
    (W : CubicTestWeight) (J : ℝ → ℕ)
    (hmain : (fun T ↦ cubicAFECompletionSchedulePrincipalPart W J T -
        cubicMainConstant W) =o[atTop] (fun _T ↦ (1 : ℝ)))
    (hrem : cubicAFECompletionScheduleRemainder W J =o[atTop]
      (fun T : ℝ ↦ T)) :
    (fun T ↦ cubicMollifiedSecondMoment W T -
      cubicMainConstant W * T) =o[atTop] (fun T : ℝ ↦ T) := by
  exact cubic_actual_long_mollifier_asymptotic_of_exact_inputs W
    (cubicAFECompletionSchedulePrincipalPart W J)
    (cubicAFECompletionScheduleRemainder W J)
    (cubicMollifiedSecondMoment_eq_completionSchedule_principal_remainder W J)
    hmain hrem

/-- Constant-depth specialization of the scheduled final interface. -/
theorem cubic_actual_long_mollifier_asymptotic_of_fixedDepth_estimates
    (W : CubicTestWeight) (J : ℕ)
    (hmain : (fun T ↦ cubicAFEFixedDepthPrincipalPart W J T -
        cubicMainConstant W) =o[atTop] (fun _T ↦ (1 : ℝ)))
    (hrem : cubicAFEFixedDepthRemainder W J =o[atTop]
      (fun T : ℝ ↦ T)) :
    (fun T ↦ cubicMollifiedSecondMoment W T -
      cubicMainConstant W * T) =o[atTop] (fun T : ℝ ↦ T) := by
  exact cubic_actual_long_mollifier_asymptotic_of_completionSchedule_estimates
    W (fun _T ↦ J) hmain hrem

end PrimeNumberTheorem.MWKFCubic
