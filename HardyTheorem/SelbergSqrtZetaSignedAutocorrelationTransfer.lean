import HardyTheorem.SelbergLagDyadicGeometry
import HardyTheorem.SelbergSqrtZetaGoodWindowMeasure
import HardyTheorem.SelbergSqrtZetaSignedApproximation
import HardyTheorem.SelbergSqrtZetaSignedModelContinuity
import MathlibAux.AutocorrelationApproximation

/-!
# Transfer of signed autocorrelations to the finite theta model

The first zeta approximation is uniform on one positive dyadic interval.
The triangular lag geometry keeps both arguments of every autocorrelation
inside that interval.  Consequently an explicit uniform model bound converts
the pointwise zeta approximation into an integrated autocorrelation error.
-/

open MeasureTheory Set

namespace HardyTheorem

/-- On every admissible triangular lag section, the autocorrelation of the
actual square-root-zeta mollified Hardy function differs from the finite
theta-model autocorrelation by an explicit uniform error. -/
theorem
    exists_abs_integral_selbergSqrtZetaMollifiedAutocorrelation_sub_signedThetaModel_le :
    ∃ kappa C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, 2 ≤ X → ∀ T H tau v M : ℝ,
        T0 ≤ T → 0 ≤ H → H ≤ T →
        tau ∈ Icc (-H) H →
        v ∈ Icc (max 0 (-tau)) (min H (H - tau)) →
        0 ≤ M →
        (∀ x ∈ Icc T (2 * T),
          |selbergSqrtZetaSignedThetaModel kappa T X x| ≤ M) →
        |(∫ x in T + v..(2 * T - H) + v,
              selbergSqrtZetaMollifiedHardyZ X x *
                selbergSqrtZetaMollifiedHardyZ X (x + tau)) -
            ∫ x in T + v..(2 * T - H) + v,
              selbergSqrtZetaSignedThetaModel kappa T X x *
                selbergSqrtZetaSignedThetaModel kappa T X (x + tau)| ≤
          (T - H) *
            (2 * (M + 4 * C * X / Real.sqrt T) *
              (4 * C * X / Real.sqrt T)) := by
  obtain ⟨kappa, C, T0, hC, hT0, happ⟩ :=
    exists_abs_selbergSqrtZetaMollifiedHardyZ_sub_signedThetaModel_le_four_mul
  refine ⟨kappa, C, T0, hC, hT0, ?_⟩
  intro X hX T H tau v M hT hH hHT htau hv hM hmodel
  let F : ℝ → ℝ := selbergSqrtZetaMollifiedHardyZ X
  let P : ℝ → ℝ := selbergSqrtZetaSignedThetaModel kappa T X
  let eps : ℝ := 4 * C * X / Real.sqrt T
  let A : ℝ := T + v
  let B : ℝ := (2 * T - H) + v
  have hTpos : 0 < T := lt_of_lt_of_le (by norm_num) (hT0.trans hT)
  have heps : 0 ≤ eps := by
    dsimp only [eps]
    positivity
  have hAB : A ≤ B := by
    dsimp only [A, B]
    linarith
  have hcontrol :
      Icc (min A (A + tau)) (max B (B + tau)) ⊆ Icc T (2 * T) := by
    dsimp only [A, B]
    exact selberg_lag_controlInterval_subset_dyadic htau hv
  have hPcont : ContinuousOn P
      (Icc (min A (A + tau)) (max B (B + tau))) := by
    exact
      (continuousOn_selbergSqrtZetaSignedThetaModel_Icc_T_two_mul_T
        kappa T X hTpos).mono hcontrol
  have hFcont : Continuous F :=
    continuous_selbergSqrtZetaMollifiedHardyZ X
  have happrox : ∀ x ∈
      Icc (min A (A + tau)) (max B (B + tau)),
      |F x - P x| ≤ eps := by
    intro x hx
    exact happ X hX T x hT (hcontrol hx)
  have hPbound : ∀ x ∈
      Icc (min A (A + tau)) (max B (B + tau)),
      |P x| ≤ M + eps := by
    intro x hx
    exact (hmodel x (hcontrol hx)).trans (le_add_of_nonneg_right heps)
  have hFbound : ∀ x ∈
      Icc (min A (A + tau)) (max B (B + tau)),
      |F x| ≤ M + eps := by
    intro x hx
    calc
      |F x| = |(F x - P x) + P x| := by ring_nf
      _ ≤ |F x - P x| + |P x| := abs_add_le _ _
      _ ≤ eps + M := add_le_add (happrox x hx) (hmodel x (hcontrol hx))
      _ = M + eps := by ring
  have hM' : 0 ≤ M + eps := add_nonneg hM heps
  have htransfer :=
    MathlibAux.abs_integral_mul_shift_sub_mul_shift_le_of_continuousOn
      hFcont.continuousOn hPcont hAB heps hM'
      happrox hFbound hPbound
  simpa only [F, P, A, B, eps, show
      ((2 * T - H) + v) - (T + v) = T - H by ring] using htransfer

end HardyTheorem
