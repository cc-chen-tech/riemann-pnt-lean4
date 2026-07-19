import PrimeNumberTheorem.MollifiedZetaError

open Complex
open Filter Topology
open scoped Interval

namespace PrimeNumberTheorem
namespace CarlsonZeroDensity

/-- Carlson's auxiliary zero detector `h_X = 1 - f_X^2`, where
`f_X = zeta * M_X - 1`. -/
noncomputable def carlsonZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  1 - mollifiedZetaError X s ^ 2

/-- Pole-free Carlson detector on the right half-plane.  Replacing zeta by
its analytic pole unit makes this function analytic across `s = 1`; away
from `0` and `1` it is `(s - 1)^2 * carlsonZeroDetector X s`. -/
noncomputable def regularizedCarlsonZeroDetector (X : ℕ) (s : ℂ) : ℂ :=
  let q := ZeroFreeRegion.riemannZetaPoleUnitAtOne s
  let m := mobiusMollifier X s
  q * m * (2 * (s - 1) - q * m)

/-- The pole-free Carlson detector is analytic on every right half-plane
contained in `Re(s) > 0`. -/
theorem analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
    {theta : ℝ} (htheta : 0 ≤ theta) (X : ℕ) :
    AnalyticOnNhd ℂ (regularizedCarlsonZeroDetector X)
      {s : ℂ | theta < s.re} := by
  intro s hs
  have hq : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne s :=
    ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt htheta s hs
  have hm : AnalyticAt ℂ (mobiusMollifier X) s :=
    analyticAt_mobiusMollifier X s
  have hlinear : AnalyticAt ℂ (fun z : ℂ => 2 * (z - 1)) s :=
    analyticAt_const.mul (analyticAt_id.sub analyticAt_const)
  unfold regularizedCarlsonZeroDetector
  exact (hq.mul hm).mul (hlinear.sub (hq.mul hm))

/-- Globally the pole-free detector is meromorphic.  Its possible behavior at
`0` is harmless for Carlson rectangles, which lie in `Re(s) > 1/2`. -/
theorem meromorphic_regularizedCarlsonZeroDetector (X : ℕ) :
    Meromorphic (regularizedCarlsonZeroDetector X) := by
  intro s
  have hcompleted : MeromorphicAt completedRiemannZeta₀ s :=
    (differentiable_completedZeta₀.analyticAt s).meromorphicAt
  have hid : MeromorphicAt (fun z : ℂ => z) s :=
    analyticAt_id.meromorphicAt
  have honeDiv : MeromorphicAt (fun z : ℂ => 1 / z) s :=
    (MeromorphicAt.const 1 s).div hid
  have hgammaInv : MeromorphicAt (fun z : ℂ => (Gammaℝ z)⁻¹) s :=
    (differentiable_Gammaℝ_inv.analyticAt s).meromorphicAt
  have hregular : MeromorphicAt ZeroFreeRegion.riemannZetaRegularAtOne s := by
    unfold ZeroFreeRegion.riemannZetaRegularAtOne
    exact (hcompleted.sub honeDiv).mul hgammaInv
  have hq : MeromorphicAt ZeroFreeRegion.riemannZetaPoleUnitAtOne s := by
    unfold ZeroFreeRegion.riemannZetaPoleUnitAtOne
    exact (((analyticAt_id.sub analyticAt_const).meromorphicAt.mul hregular).add
      hgammaInv)
  have hm : MeromorphicAt (mobiusMollifier X) s :=
    (analyticAt_mobiusMollifier X s).meromorphicAt
  have hlinear : MeromorphicAt (fun z : ℂ => 2 * (z - 1)) s :=
    (analyticAt_const.mul
      (analyticAt_id.sub analyticAt_const)).meromorphicAt
  unfold regularizedCarlsonZeroDetector
  exact (hq.mul hm).mul (hlinear.sub (hq.mul hm))

/-- The detector factors through zeta, so every zeta zero is a detector zero. -/
theorem carlsonZeroDetector_eq_zeta_mul_mollifier_factorization
    (X : ℕ) (s : ℂ) :
    carlsonZeroDetector X s =
      (riemannZeta s * mobiusMollifier X s) *
        (2 - riemannZeta s * mobiusMollifier X s) := by
  unfold carlsonZeroDetector mollifiedZetaError
  ring

/-- Away from the removable points, the analytic detector is the original
Carlson detector multiplied by the square cancelling its pole at `1`. -/
theorem regularizedCarlsonZeroDetector_eq_sub_one_sq_mul
    (X : ℕ) {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) :
    regularizedCarlsonZeroDetector X s =
      (s - 1) ^ 2 * carlsonZeroDetector X s := by
  unfold regularizedCarlsonZeroDetector
  rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
    hs0 hs1,
    carlsonZeroDetector_eq_zeta_mul_mollifier_factorization]
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

/-- Every nontrivial zeta zero occurs in the pole-free Carlson detector with
at least its zeta multiplicity. -/
theorem analyticOrderNatAt_riemannZeta_le_regularizedCarlsonZeroDetector
    {X : ℕ} {rho : ℂ} (hX : 1 ≤ X)
    (hrho : RiemannHypothesis.IsNontrivialZero rho) :
    analyticOrderNatAt riemannZeta rho ≤
      analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho := by
  let q : ℂ → ℂ := ZeroFreeRegion.riemannZetaPoleUnitAtOne
  let complement : ℂ → ℂ := fun s =>
    2 * (s - 1) - q s * mobiusMollifier X s
  let g : ℂ → ℂ := fun s =>
    (s - 1) * (mobiusMollifier X s * complement s)
  have hrho0 : rho ≠ 0 := by
    intro hzero
    subst rho
    have hpos := hrho.2.1
    norm_num at hpos
  have hrho1 : rho ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp at hre
    linarith [hrho.2.2]
  have hzeta : AnalyticAt ℂ riemannZeta rho :=
    ZeroFreeRegion.analyticOnNhd_riemannZeta_ne_one rho hrho1
  have hq : AnalyticAt ℂ q rho := by
    dsimp [q]
    exact ZeroFreeRegion.analyticOnNhd_riemannZetaPoleUnitAtOne_re_gt
      (θ := 0) le_rfl rho hrho.2.1
  have hm : AnalyticAt ℂ (mobiusMollifier X) rho :=
    analyticAt_mobiusMollifier X rho
  have hcomplement : AnalyticAt ℂ complement rho := by
    dsimp [complement]
    exact (analyticAt_const.mul (analyticAt_id.sub analyticAt_const)).sub
      (hq.mul hm)
  have hq_rho : q rho = 0 := by
    dsimp [q]
    rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hrho0 hrho1, hrho.1, mul_zero]
  have hcomplement_ne : complement rho ≠ 0 := by
    dsimp [complement]
    rw [hq_rho, zero_mul, sub_zero]
    exact mul_ne_zero (by norm_num) (sub_ne_zero.mpr hrho1)
  have hcomplement_order_zero : analyticOrderAt complement rho = 0 :=
    hcomplement.analyticOrderAt_eq_zero.mpr hcomplement_ne
  have hm_order_ne_top : analyticOrderAt (mobiusMollifier X) rho ≠ ⊤ :=
    analyticOrderAt_mobiusMollifier_ne_top X hX rho
  have hm_complement_order_ne_top :
      analyticOrderAt ((mobiusMollifier X) * complement) rho ≠ ⊤ := by
    rw [analyticOrderAt_mul hm hcomplement, hcomplement_order_zero, add_zero]
    exact hm_order_ne_top
  have hsub : AnalyticAt ℂ (fun s : ℂ => s - 1) rho :=
    analyticAt_id.sub analyticAt_const
  have hsub_order_zero :
      analyticOrderAt (fun s : ℂ => s - 1) rho = 0 :=
    hsub.analyticOrderAt_eq_zero.mpr (sub_ne_zero.mpr hrho1)
  have hg : AnalyticAt ℂ g rho := by
    dsimp [g]
    exact hsub.mul (hm.mul hcomplement)
  have hg_order_ne_top : analyticOrderAt g rho ≠ ⊤ := by
    rw [show analyticOrderAt g rho =
        analyticOrderAt (fun s : ℂ => s - 1) rho +
          analyticOrderAt ((mobiusMollifier X) * complement) rho by
      exact analyticOrderAt_mul hsub (hm.mul hcomplement),
      hsub_order_zero, zero_add]
    exact hm_complement_order_ne_top
  have hq_eventually :
      q =ᶠ[𝓝 rho]
        fun s : ℂ => (s - 1) * riemannZeta s := by
    filter_upwards [eventually_ne_nhds hrho0, eventually_ne_nhds hrho1]
      with s hs0 hs1
    exact ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta
      hs0 hs1
  have hfactor :
      regularizedCarlsonZeroDetector X =ᶠ[𝓝 rho]
        riemannZeta * g := by
    filter_upwards [hq_eventually] with s hqs
    simp only [Pi.mul_apply]
    change ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
        mobiusMollifier X s *
          (2 * (s - 1) - ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
            mobiusMollifier X s) =
      riemannZeta s *
        ((s - 1) * (mobiusMollifier X s *
          (2 * (s - 1) - ZeroFreeRegion.riemannZetaPoleUnitAtOne s *
            mobiusMollifier X s)))
    rw [show ZeroFreeRegion.riemannZetaPoleUnitAtOne s =
        (s - 1) * riemannZeta s by exact hqs]
    ring
  have hzeta_order_ne_top : analyticOrderAt riemannZeta rho ≠ ⊤ :=
    ZeroFreeRegion.analyticOrderAt_riemannZeta_ne_top_of_ne_one hrho1
  have horder_nat :
      analyticOrderNatAt (regularizedCarlsonZeroDetector X) rho =
        analyticOrderNatAt (riemannZeta * g) rho := by
    unfold analyticOrderNatAt
    rw [analyticOrderAt_congr hfactor]
  rw [horder_nat,
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

/-- Away from the removable points, the logarithmic size of the pole-free
detector differs from the original Carlson detector only by the explicit
geometric factor `(s - 1)^2`. -/
theorem log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
    {X : ℕ} {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hdet : carlsonZeroDetector X s ≠ 0) :
    Real.log ‖regularizedCarlsonZeroDetector X s‖ ≤
      2 * Real.log ‖s - 1‖ + ‖mollifiedZetaError X s‖ ^ 2 := by
  rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X hs0 hs1,
    norm_mul, norm_pow,
    Real.log_mul
      (pow_ne_zero 2 (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hs1)))
      (norm_ne_zero_iff.mpr hdet),
    Real.log_pow]
  simpa using add_le_add_right
    (log_norm_carlsonZeroDetector_le_norm_mollifiedZetaError_sq X s)
    (2 * Real.log ‖s - 1‖)

/-- The pole-free detector is continuous on every vertical line in the right
half-plane. -/
theorem continuous_regularizedCarlsonZeroDetector_verticalLine
    (X : ℕ) {sigma : ℝ} (hsigma0 : 0 < sigma) :
    Continuous (fun t : ℝ =>
      regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)) := by
  rw [continuous_iff_continuousAt]
  intro t
  have han : AnalyticAt ℂ (regularizedCarlsonZeroDetector X)
      ((sigma : ℂ) + Complex.I * (t : ℂ)) :=
    analyticOnNhd_regularizedCarlsonZeroDetector_re_gt
      (theta := (0 : ℝ)) le_rfl X _ (by simpa using hsigma0)
  have hmap : ContinuousAt
      (fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ)) t := by
    fun_prop
  simpa [Function.comp_def] using han.continuousAt.comp_of_eq hmap rfl

/-- On a zero-free left boundary, the pole-free detector's logarithmic
integral is controlled by the explicit regularization factor and the same
mollified-zeta mean square used for Carlson's original detector. -/
theorem integral_log_norm_regularizedCarlsonZeroDetector_le_geometric_add_meanSquare
    {X : ℕ} {sigma a b : ℝ} (hab : a ≤ b)
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≠ 1)
    (hboundary : ∀ t ∈ Set.Icc a b,
      carlsonZeroDetector X ((sigma : ℂ) + Complex.I * t) ≠ 0) :
    (∫ t in a..b,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
      2 * (∫ t in a..b,
        Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) +
      ∫ t in a..b,
        ‖mollifiedZetaError X
          ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
  have hregCont :=
    continuous_regularizedCarlsonZeroDetector_verticalLine X hsigma0
  have hzetaCont : Continuous (fun t : ℝ =>
      riemannZeta ((sigma : ℂ) + Complex.I * t)) := by
    simpa [carlsonZetaRemainder] using
      (continuous_carlsonZetaRemainder_verticalLine 0 sigma hsigma1)
  have herrorCont : Continuous (fun t : ℝ =>
      mollifiedZetaError X ((sigma : ℂ) + Complex.I * t)) := by
    unfold mollifiedZetaError
    exact (hzetaCont.mul
      (continuous_mobiusMollifier_verticalLine X sigma)).sub continuous_const
  have hpointNe {t : ℝ} :
      (sigma : ℂ) + Complex.I * (t : ℂ) ≠ 0 := by
    intro hzero
    have hre := congrArg Complex.re hzero
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      Complex.zero_re] at hre
    linarith
  have hpointOne {t : ℝ} :
      (sigma : ℂ) + Complex.I * (t : ℂ) ≠ 1 := by
    intro hone
    have hre := congrArg Complex.re hone
    simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      Complex.one_re] at hre
    apply hsigma1
    linarith
  have hregNe {t : ℝ} (ht : t ∈ Set.Icc a b) :
      regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ)) ≠ 0 := by
    rw [regularizedCarlsonZeroDetector_eq_sub_one_sq_mul X
      hpointNe hpointOne]
    exact mul_ne_zero (pow_ne_zero 2 (sub_ne_zero.mpr hpointOne))
      (hboundary t ht)
  have hlogRegContOn : ContinuousOn (fun t : ℝ =>
      Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖) (Set.Icc a b) := by
    intro t ht
    have hlog : ContinuousAt Real.log
        ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ))‖ :=
      Real.continuousAt_log (norm_ne_zero_iff.mpr (hregNe ht))
    have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        (regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * (t : ℂ))) :=
      hlog.comp' continuous_norm.continuousAt
    exact (ContinuousAt.comp'
      (f := fun u : ℝ => regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * u))
      hlogNorm hregCont.continuousAt).continuousWithinAt
  have hgeomCont : Continuous (fun t : ℝ =>
      Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖) := by
    rw [continuous_iff_continuousAt]
    intro t
    have hlog : ContinuousAt Real.log
        ‖(sigma : ℂ) + Complex.I * (t : ℂ) - 1‖ :=
      Real.continuousAt_log
        (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpointOne))
    have hlogNorm : ContinuousAt (fun z : ℂ => Real.log ‖z‖)
        ((sigma : ℂ) + Complex.I * (t : ℂ) - 1) :=
      hlog.comp' continuous_norm.continuousAt
    have hmap : ContinuousAt
        (fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ) - 1) t := by
      fun_prop
    exact ContinuousAt.comp'
      (f := fun u : ℝ => (sigma : ℂ) + Complex.I * (u : ℂ) - 1)
      hlogNorm hmap
  have hleftInt : IntervalIntegrable (fun t : ℝ =>
      Real.log ‖regularizedCarlsonZeroDetector X
        ((sigma : ℂ) + Complex.I * t)‖)
      MeasureTheory.volume a b :=
    hlogRegContOn.intervalIntegrable_of_Icc hab
  have hgeomInt : IntervalIntegrable (fun t : ℝ =>
      2 * Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖)
      MeasureTheory.volume a b :=
    (continuous_const.mul hgeomCont).intervalIntegrable a b
  have herrorInt : IntervalIntegrable (fun t : ℝ =>
      ‖mollifiedZetaError X
        ((sigma : ℂ) + Complex.I * t)‖ ^ 2)
      MeasureTheory.volume a b :=
    (herrorCont.norm.pow 2).intervalIntegrable a b
  calc
    (∫ t in a..b,
        Real.log ‖regularizedCarlsonZeroDetector X
          ((sigma : ℂ) + Complex.I * t)‖) ≤
        ∫ t in a..b,
          2 * Real.log ‖(sigma : ℂ) + Complex.I * t - 1‖ +
            ‖mollifiedZetaError X
              ((sigma : ℂ) + Complex.I * t)‖ ^ 2 := by
      exact intervalIntegral.integral_mono_on hab hleftInt
        (hgeomInt.add herrorInt) fun t ht =>
          log_norm_regularizedCarlsonZeroDetector_le_two_log_norm_sub_one_add_error_sq
            hpointNe hpointOne (hboundary t ht)
    _ = _ := by
      rw [intervalIntegral.integral_add hgeomInt herrorInt,
        intervalIntegral.integral_const_mul]

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
