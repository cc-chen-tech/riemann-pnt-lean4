import PrimeNumberTheorem.MollifiedZetaError

open Complex
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Carlson's auxiliary zero detector `h_X = 1 - f_X^2`, where
`f_X = zeta * M_X - 1`. -/
noncomputable def carlsonZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  1 - mollifiedZetaError X s ^ 2

/-- The detector factors through zeta, so every zeta zero is a detector zero. -/
theorem carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
    (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s =
      (riemannZeta s * mobiusMollifier X s) *
        (2 - riemannZeta s * mobiusMollifier X s) := by
  unfold carlsonZeroDetector mollifiedZetaError
  ring

theorem carlsonZeroDetector_eq_zero_of_riemannZeta_eq_zero
    {X : ℕ} {s : ℂ} (hs : riemannZeta s = 0) :
    carlsonZeroDetector X s = 0 := by
  rw [carlsonZeroDetector_eq_zeta_mul_mollifier_factorization, hs]
  ring

/-- Every nontrivial zeta zero occurs in Carlson's detector with at least its
zeta multiplicity.  The extra mollifier factor may increase the multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_le_carlsonZeroDetector
    {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (carlsonZeroDetector X) rho := by
  let g : ℂ → ℂ := fun s =>
    mobiusMollifier X s *
      (2 - riemannZeta s * mobiusMollifier X s)
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hmollifier : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hcomplement : AnalyticAt ℂ
      (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho :=
    analyticAt_const.sub (hzeta.mul hmollifier)
  have hg : AnalyticAt ℂ g rho := by
    dsimp [g]
    exact hmollifier.mul hcomplement
  have hzeta_order_ne_top : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hrho1
  have hcomplement_ne :
      (2 - riemannZeta rho * mobiusMollifier X rho : ℂ) ≠ 0 := by
    rw [hrho.1]
    norm_num
  have hcomplement_order_zero :
      analyticOrderAt
        (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho = 0 :=
    hcomplement.analyticOrderAt_eq_zero.mpr hcomplement_ne
  have hmollifier_order_ne_top :
      analyticOrderAt (mobiusMollifier X) rho ≠ ⊤ :=
    analyticOrderAt_mobiusMollifier_ne_top X hX rho
  have hg_order_ne_top : analyticOrderAt g rho ≠ ⊤ := by
    rw [show analyticOrderAt g rho =
        analyticOrderAt (mobiusMollifier X) rho +
          analyticOrderAt
            (fun s : ℂ => 2 - riemannZeta s * mobiusMollifier X s) rho by
      exact analyticOrderAt_mul hmollifier hcomplement,
      hcomplement_order_zero, add_zero]
    exact hmollifier_order_ne_top
  have hfactor : carlsonZeroDetector X = riemannZeta * g := by
    funext s
    simp only [Pi.mul_apply]
    simpa [g, mul_assoc] using
      carlsonZeroDetector_eq_zeta_mul_mollifier_factorization X s
  rw [hfactor,
    analyticOrderNatAt_mul hzeta hg hzeta_order_ne_top hg_order_ne_top]
  exact Nat.le_add_right _ _

/-- The pointwise logarithmic majorant used on the left edge of Littlewood's
rectangle: `log |h_X|` is controlled by the square entering the mean value
estimate for `f_X`. -/
theorem log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
    (X : ℕ) (s : ℂ) :
    Real.log ‖carlsonZeroDetector X s‖ ≤
      ‖mollifiedZetaError X s‖ ^ 2 := by
  let f : ℂ := mollifiedZetaError X s
  by_cases hdet : carlsonZeroDetector X s = 0
  · rw [hdet, norm_zero, Real.log_zero]
    exact sq_nonneg ‖mollifiedZetaError X s‖
  · have hnorm_pos : 0 < ‖carlsonZeroDetector X s‖ :=
      norm_pos_iff.mpr hdet
    have hnorm_le : ‖carlsonZeroDetector X s‖ ≤ 1 + ‖f‖ ^ 2 := by
      change ‖1 - f ^ 2‖ ≤ 1 + ‖f‖ ^ 2
      calc
        ‖1 - f ^ 2‖ ≤ ‖(1 : ℂ)‖ + ‖f ^ 2‖ := norm_sub_le _ _
        _ = 1 + ‖f‖ ^ 2 := by simp
    calc
      Real.log ‖carlsonZeroDetector X s‖ ≤
          Real.log (1 + ‖f‖ ^ 2) :=
        Real.log_le_log hnorm_pos hnorm_le
      _ ≤ ‖f‖ ^ 2 := by
        simpa using Real.log_le_sub_one_of_pos
          (show 0 < 1 + ‖f‖ ^ 2 by positivity)
      _ = ‖mollifiedZetaError X s‖ ^ 2 := rfl

/-- Away from the zeta pole, the mollified zeta error is continuous on a
vertical line. -/
theorem continuous_mollifiedZetaError_verticalLine
    (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
  have hzeta : Continuous (fun t : ℝ =>
      riemannZeta ((sigma : ℂ) + Complex.I * t)) := by
    simpa [carlsonZetaRemainder] using
      (continuous_carlsonZetaRemainder_verticalLine 0 sigma hsigma1)
  have hmollifier := continuous_mobiusMollifier_verticalLine X sigma
  unfold mollifiedZetaError
  exact (hzeta.mul hmollifier).sub continuous_const

theorem continuous_carlsonZeroDetector_verticalLine
    (X : ℕ) (sigma : ℝ) (hsigma1 : sigma ≠ 1) :
    Continuous (fun t : ℝ =>
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t)) := by
  unfold carlsonZeroDetector
  exact continuous_const.sub
    ((continuous_mollifiedZetaError_verticalLine X sigma hsigma1).pow 2)

/-- On a zero-free vertical boundary, Littlewood's logarithmic left-edge
integral is bounded by the mollified-zeta second moment. -/
theorem integral_log_norm_carlsonZeroDetector_le_meanSquare
    {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    ∫ t in a..b,
        Real.log ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ ≤
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
  have hdetCont := continuous_carlsonZeroDetector_verticalLine X sigma hsigma1
  have herrCont := continuous_mollifiedZetaError_verticalLine X sigma hsigma1
  have hlogContOn : ContinuousOn (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖) (Set.Icc a b) := by
    intro t ht
    have hlogCont : ContinuousAt Real.log
        ‖carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr (hboundary t ht))
    have hlogNormCont : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        (carlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)) :=
      hlogCont.comp' continuous_norm.continuousAt
    exact (ContinuousAt.comp'
      (f := fun u : ℝ =>
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * u))
      hlogNormCont hdetCont.continuousAt).continuousWithinAt
  have hlogInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖carlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b :=
    hlogContOn.intervalIntegrable_of_Icc hab
  have hsquareInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (herrCont.norm.pow 2).intervalIntegrable a b
  exact intervalIntegral.integral_mono_on hab hlogInt hsquareInt
    (fun t _ =>
      log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq
        X ((sigma : ℂ) + Complex.I * t))

/-- The verified mollified-zeta mean square gives the Carlson/Littlewood
left-edge logarithmic bound with the same endpoint expression. -/
theorem exists_integral_log_norm_carlsonZeroDetector_le_endpoint :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (X : ℕ) (sigma a b x : ℝ),
      1 ≤ X → a ≤ b → 1 / 2 < sigma → sigma < 1 → 2 ≤ x →
      (∀ t ∈ Set.Icc a b, |t| ≤ x / 2 ∧ x ≤ 2 * |t|) →
      (∀ t ∈ Set.Icc a b,
        carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) →
        ∫ t in a..b,
            Real.log ‖carlsonZeroDetector X
              ((sigma : ℂ) + Complex.I * t)‖ ≤
          2 * (((b - a) + 4 * Real.pi) *
            (2 * ((min X (Nat.floor x) + 1 : ℕ) : ℝ) ^
                (1 - 2 * sigma) *
              ((((Nat.floor x) * X : ℕ) : ℝ) *
                (1 + Real.log (Nat.floor x * X)) ^ 3))) +
          2 * ((C * x ^ (-sigma)) ^ 2 *
            (((b - a) + 4 * Real.pi) *
              (2 * (1 +
                ((X : ℝ) ^ (2 - 2 * sigma) - 1) /
                  (2 - 2 * sigma))))) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_mollifiedZetaError_meanSquare_le_endpoint
  refine ⟨C, hC, ?_⟩
  intro X sigma a b x hX hab hsigma hsigma1 hx hheight hboundary
  exact (integral_log_norm_carlsonZeroDetector_le_meanSquare
    hab (ne_of_lt hsigma1) hboundary).trans
      (hmean X sigma a b x hX hab hsigma hsigma1 hx hheight)

end CarlsonZeroDensity
end PrimeNumberTheorem
