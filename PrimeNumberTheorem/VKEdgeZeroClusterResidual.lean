import PrimeNumberTheorem.VKEdgeZeroDensityResidualL2

open Complex MeasureTheory Set
open Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Zeros in the positive-height residual package lying in the open
real-part band immediately below the target scale `beta`. -/
def positiveZeroDensityResidualTopBandCluster
    (rho0 : ℂ) (beta sigma T delta : ℝ) : Finset ℂ :=
  (positiveZeroDensityResidualFinset rho0 sigma T).filter fun rho =>
    beta - delta < rho.re

/-- The complementary zeros in the positive-height residual package. This
set has the real-part gap needed for exponential decay by construction. -/
def positiveZeroDensityResidualLeftRemainder
    (rho0 : ℂ) (beta sigma T delta : ℝ) : Finset ℂ :=
  (positiveZeroDensityResidualFinset rho0 sigma T).filter fun rho =>
    rho.re ≤ beta - delta

/-- A normalized multiplicity-weighted zero contribution over an arbitrary
finite package. -/
def normalizedPositiveZeroDensityContributionOn
    (S : Finset ℂ) (beta y : ℝ) : ℂ :=
  (Real.exp (-beta * y) : ℂ) *
    ∑ rho ∈ S,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        (Real.exp y : ℂ) ^ rho / rho

/-- The top band and its left remainder partition the entire positive-height
residual package. -/
theorem positiveZeroDensityResidualTopBandCluster_union_leftRemainder
    (rho0 : ℂ) (beta sigma T delta : ℝ) :
    positiveZeroDensityResidualTopBandCluster
        rho0 beta sigma T delta ∪
      positiveZeroDensityResidualLeftRemainder
        rho0 beta sigma T delta =
      positiveZeroDensityResidualFinset rho0 sigma T := by
  classical
  ext rho
  simp only [positiveZeroDensityResidualTopBandCluster,
    positiveZeroDensityResidualLeftRemainder, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · rintro (⟨hrho, _⟩ | ⟨hrho, _⟩)
    · exact hrho
    · exact hrho
  · intro hrho
    exact (lt_or_ge (beta - delta) rho.re).elim
      (fun h => Or.inl ⟨hrho, h⟩)
      (fun h => Or.inr ⟨hrho, h⟩)

/-- The multiplicity of the top band is bounded by the full Carlson counting
function. Carlson controls the size of the cluster, not its internal phase
cancellation. -/
theorem sum_order_positiveZeroDensityResidualTopBandCluster_le_count
    (rho0 : ℂ) (beta sigma T delta : ℝ) :
    (∑ rho ∈ positiveZeroDensityResidualTopBandCluster
        rho0 beta sigma T delta,
      analyticOrderNatAt riemannZeta rho) ≤
    ZeroDensity.zeroDensityCount sigma T := by
  classical
  unfold positiveZeroDensityResidualTopBandCluster
  unfold positiveZeroDensityResidualFinset
  unfold ZeroDensity.zeroDensityCount
  exact Finset.sum_le_sum_of_subset_of_nonneg
    ((Finset.filter_subset _ _).trans
      (Finset.erase_subset rho0
        (ZeroDensity.zeroDensityZerosFinset sigma T)))
    (fun _ _ _ => Nat.zero_le _)

/-- Exact decomposition of the positive-height residual into its top
real-part cluster and the automatically separated left remainder. -/
theorem
    normalizedPositiveZeroDensityResidualContribution_eq_cluster_add_left
    (rho0 : ℂ) (beta sigma T delta y : ℝ) :
    normalizedPositiveZeroDensityResidualContribution
        rho0 beta sigma T y =
      normalizedPositiveZeroDensityContributionOn
          (positiveZeroDensityResidualTopBandCluster
            rho0 beta sigma T delta) beta y +
        normalizedPositiveZeroDensityContributionOn
          (positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta) beta y := by
  classical
  let f : ℂ → ℂ := fun rho =>
    (analyticOrderNatAt riemannZeta rho : ℂ) *
      (Real.exp y : ℂ) ^ rho / rho
  have hsplit :
      (∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T, f rho) =
        (∑ rho ∈ positiveZeroDensityResidualTopBandCluster
            rho0 beta sigma T delta, f rho) +
          ∑ rho ∈ positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta, f rho := by
    simpa only [positiveZeroDensityResidualTopBandCluster,
      positiveZeroDensityResidualLeftRemainder, not_lt] using
      (Finset.sum_filter_add_sum_filter_not
        (positiveZeroDensityResidualFinset rho0 sigma T)
        (fun rho : ℂ => beta - delta < rho.re) f).symm
  unfold normalizedPositiveZeroDensityResidualContribution
  unfold normalizedPositiveZeroDensityContributionOn
  change
    (Real.exp (-beta * y) : ℂ) *
        (∑ rho ∈ positiveZeroDensityResidualFinset rho0 sigma T, f rho) =
      (Real.exp (-beta * y) : ℂ) *
          (∑ rho ∈ positiveZeroDensityResidualTopBandCluster
            rho0 beta sigma T delta, f rho) +
        (Real.exp (-beta * y) : ℂ) *
          ∑ rho ∈ positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta, f rho
  rw [hsplit, mul_add]

private theorem norm_normalizedPositiveZeroDensityContributionOn_le_count
    {S : Finset ℂ} {beta sigma T delta y : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hy : 0 ≤ y)
    (hsubset : S ⊆ ZeroDensity.zeroDensityZerosFinset sigma T)
    (hgap : ∀ rho ∈ S, rho.re ≤ beta - delta) :
    ‖normalizedPositiveZeroDensityContributionOn S beta y‖ ≤
      2 * Real.exp (-delta * y) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  classical
  let Z : ℂ :=
    ∑ rho ∈ S,
      (analyticOrderNatAt riemannZeta rho : ℂ) *
        (Real.exp y : ℂ) ^ rho / rho
  have hsum :
      ‖Z‖ ≤
        2 * Real.exp ((beta - delta) * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
    calc
      ‖Z‖ ≤
          ∑ rho ∈ S,
            ‖(analyticOrderNatAt riemannZeta rho : ℂ) *
                (Real.exp y : ℂ) ^ rho / rho‖ := by
        dsimp only [Z]
        exact norm_sum_le _ _
      _ = ∑ rho ∈ S,
            (analyticOrderNatAt riemannZeta rho : ℝ) *
              (Real.exp y) ^ rho.re / ‖rho‖ := by
        refine Finset.sum_congr rfl fun rho _ => ?_
        exact ZeroForcedOscillation.norm_natCast_mul_cpow_div
          (Real.exp y) (Real.exp_pos y) rho _
      _ ≤ ∑ rho ∈ S,
            2 * Real.exp ((beta - delta) * y) *
              (analyticOrderNatAt riemannZeta rho : ℝ) := by
        refine Finset.sum_le_sum fun rho hrho => ?_
        have hrhoFull :
            rho ∈ ZeroDensity.zeroDensityZerosFinset sigma T :=
          hsubset hrho
        have hre : sigma < rho.re :=
          (ZeroDensity.mem_zeroDensityZerosFinset.mp hrhoFull).2.2.2
        have hreHalf : 1 / 2 < rho.re := lt_of_le_of_lt hsigma hre
        have hnormHalf : 1 / 2 < ‖rho‖ :=
          hreHalf.trans_le
            ((le_abs_self rho.re).trans (Complex.abs_re_le_norm rho))
        have hinv : 1 / ‖rho‖ ≤ (2 : ℝ) := by
          have h :=
            one_div_le_one_div_of_le
              (by norm_num : (0 : ℝ) < 1 / 2) hnormHalf.le
          norm_num at h ⊢
          exact h
        have hexp :
            (Real.exp y) ^ rho.re ≤
              Real.exp ((beta - delta) * y) := by
          rw [Real.rpow_def_of_pos (Real.exp_pos y), Real.log_exp,
            mul_comm y rho.re]
          exact Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_right (hgap rho hrho) hy)
        have hcoeff :
            0 ≤ (analyticOrderNatAt riemannZeta rho : ℝ) *
              (Real.exp y) ^ rho.re :=
          mul_nonneg (Nat.cast_nonneg _)
            (Real.rpow_nonneg (Real.exp_pos y).le _)
        have hcoeffExp :
            (analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re ≤
              (analyticOrderNatAt riemannZeta rho : ℝ) *
                Real.exp ((beta - delta) * y) :=
          mul_le_mul_of_nonneg_left hexp (Nat.cast_nonneg _)
        calc
          (analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re / ‖rho‖ =
              ((analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re) * (1 / ‖rho‖) := by ring
          _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) *
                (Real.exp y) ^ rho.re) * 2 :=
            mul_le_mul_of_nonneg_left hinv hcoeff
          _ ≤ ((analyticOrderNatAt riemannZeta rho : ℝ) *
                Real.exp ((beta - delta) * y)) * 2 :=
            mul_le_mul_of_nonneg_right hcoeffExp (by norm_num)
          _ = 2 * Real.exp ((beta - delta) * y) *
                (analyticOrderNatAt riemannZeta rho : ℝ) := by ring
      _ = 2 * Real.exp ((beta - delta) * y) *
            ∑ rho ∈ S,
              (analyticOrderNatAt riemannZeta rho : ℝ) := by
        rw [Finset.mul_sum]
      _ ≤ 2 * Real.exp ((beta - delta) * y) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
        apply mul_le_mul_of_nonneg_left
        · exact_mod_cast Finset.sum_le_sum_of_subset_of_nonneg
            hsubset (fun _ _ _ => Nat.zero_le _)
        · positivity
  calc
    ‖normalizedPositiveZeroDensityContributionOn S beta y‖ =
        Real.exp (-beta * y) * ‖Z‖ := by
      simp only [normalizedPositiveZeroDensityContributionOn, Z,
        norm_mul, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
    _ ≤ Real.exp (-beta * y) *
          (2 * Real.exp ((beta - delta) * y) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) :=
      mul_le_mul_of_nonneg_left hsum (Real.exp_nonneg _)
    _ = 2 * Real.exp (-delta * y) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
      calc
        Real.exp (-beta * y) *
              (2 * Real.exp ((beta - delta) * y) *
                (ZeroDensity.zeroDensityCount sigma T : ℝ)) =
            2 * (Real.exp (-beta * y) *
              Real.exp ((beta - delta) * y)) *
                (ZeroDensity.zeroDensityCount sigma T : ℝ) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 3
          ring

/-- The left remainder satisfies the fixed-gap pointwise estimate
automatically, with no external separation hypothesis. -/
theorem norm_normalizedPositiveZeroDensityLeftRemainder_le_count
    {rho0 : ℂ} {beta sigma T delta y : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hy : 0 ≤ y) :
    ‖normalizedPositiveZeroDensityContributionOn
        (positiveZeroDensityResidualLeftRemainder
          rho0 beta sigma T delta) beta y‖ ≤
      2 * Real.exp (-delta * y) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
  apply norm_normalizedPositiveZeroDensityContributionOn_le_count
    hsigma hy
  · exact (Finset.filter_subset _ _).trans
      ((Finset.erase_subset rho0
        (ZeroDensity.zeroDensityZerosFinset sigma T)))
  · intro rho hrho
    exact (Finset.mem_filter.mp hrho).2

/-- The automatically separated left remainder has the same count-squared
local `L²` upper bound as a package with an assumed fixed gap. -/
theorem
    integral_normSq_normalizedPositiveZeroDensityLeftRemainder_le_count_sq
    {rho0 : ℂ} {beta sigma T delta a b : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    (∫ y in Icc a b,
      Complex.normSq
        (normalizedPositiveZeroDensityContributionOn
          (positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta) beta y)) ≤
      4 * (b - a) * Real.exp (-2 * delta * a) *
        (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
  classical
  let S : Finset ℂ :=
    positiveZeroDensityResidualLeftRemainder
      rho0 beta sigma T delta
  let C : ℝ :=
    4 * Real.exp (-2 * delta * a) *
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2
  have hcontinuous :
      Continuous fun y : ℝ =>
        normalizedPositiveZeroDensityContributionOn S beta y := by
    dsimp only [normalizedPositiveZeroDensityContributionOn]
    simp_rw [
      ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
        _ _ _ rfl]
    fun_prop
  have hintegrable :
      IntegrableOn
        (fun y : ℝ =>
          Complex.normSq
            (normalizedPositiveZeroDensityContributionOn S beta y))
        (Icc a b) :=
    (Complex.continuous_normSq.comp hcontinuous).integrableOn_Icc
  have hpoint (y : ℝ) (hy : y ∈ Icc a b) :
      Complex.normSq
          (normalizedPositiveZeroDensityContributionOn S beta y) ≤ C := by
    have hnorm :=
      norm_normalizedPositiveZeroDensityLeftRemainder_le_count
        (rho0 := rho0) (beta := beta) (sigma := sigma) (T := T)
        (delta := delta) (y := y) hsigma (ha.trans hy.1)
    have hexp :
        Real.exp (-delta * y) ≤ Real.exp (-delta * a) :=
      Real.exp_le_exp.mpr
        (mul_le_mul_of_nonpos_left hy.1 (neg_nonpos.mpr hdelta))
    have hbound :
        ‖normalizedPositiveZeroDensityContributionOn S beta y‖ ≤
          2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) := by
      exact hnorm.trans
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hexp (by norm_num))
          (Nat.cast_nonneg _))
    rw [Complex.normSq_eq_norm_sq]
    dsimp only [C]
    have hsquare :
        ‖normalizedPositiveZeroDensityContributionOn S beta y‖ ^ 2 ≤
          (2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ^ 2 :=
      pow_le_pow_left₀
        (norm_nonneg
          (normalizedPositiveZeroDensityContributionOn S beta y))
        hbound 2
    calc
      ‖normalizedPositiveZeroDensityContributionOn S beta y‖ ^ 2 ≤
          (2 * Real.exp (-delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ)) ^ 2 := hsquare
      _ = 4 * Real.exp (-delta * a) ^ 2 *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by ring
      _ = 4 * Real.exp (-2 * delta * a) *
            (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
        rw [show Real.exp (-delta * a) ^ 2 =
            Real.exp (-2 * delta * a) by
          rw [pow_two, ← Real.exp_add]
          congr 1
          ring]
  have hconstantIntegrable :
      IntegrableOn (fun _y : ℝ => C) (Icc a b) :=
    integrableOn_const (μ := volume) (s := Icc a b)
      measure_Icc_lt_top.ne
  have hmono :
      (∫ y in Icc a b,
          Complex.normSq
            (normalizedPositiveZeroDensityContributionOn S beta y)) ≤
        ∫ _y in Icc a b, C := by
    apply integral_mono_ae hintegrable hconstantIntegrable
    filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact hpoint y hy
  calc
    (∫ y in Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityContributionOn S beta y)) ≤
        ∫ _y in Icc a b, C := hmono
    _ = C * (b - a) := by
      rw [integral_const]
      change
        (volume.restrict (Icc a b)).real Set.univ * C =
          C * (b - a)
      rw [Measure.real, Measure.restrict_apply_univ,
        Real.volume_Icc,
        ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
      ring
    _ = 4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := by
      dsimp only [C]
      ring

private theorem
    integral_normSq_normalizedPositiveZeroDensityLeftRemainder_le_of_count_exp
    {rho0 : ℂ} {beta sigma T delta a b C kappa : ℝ}
    (hsigma : 1 / 2 ≤ sigma)
    (hdelta : 0 ≤ delta)
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hcount :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ≤
        C * Real.exp (kappa * a)) :
    (∫ y in Icc a b,
      Complex.normSq
        (normalizedPositiveZeroDensityContributionOn
          (positiveZeroDensityResidualLeftRemainder
            rho0 beta sigma T delta) beta y)) ≤
      4 * (b - a) * C ^ 2 *
        Real.exp (-2 * (delta - kappa) * a) := by
  have hbase :=
    integral_normSq_normalizedPositiveZeroDensityLeftRemainder_le_count_sq
      (rho0 := rho0) (beta := beta) (sigma := sigma) (T := T)
      (delta := delta) (a := a) (b := b)
      hsigma hdelta ha hab
  have hcountSq :
      (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 ≤
        (C * Real.exp (kappa * a)) ^ 2 :=
    pow_le_pow_left₀ (Nat.cast_nonneg _) hcount 2
  calc
    (∫ y in Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityContributionOn
            (positiveZeroDensityResidualLeftRemainder
              rho0 beta sigma T delta) beta y)) ≤
        4 * (b - a) * Real.exp (-2 * delta * a) *
          (ZeroDensity.zeroDensityCount sigma T : ℝ) ^ 2 := hbase
    _ ≤ 4 * (b - a) * Real.exp (-2 * delta * a) *
          (C * Real.exp (kappa * a)) ^ 2 := by
      exact mul_le_mul_of_nonneg_left hcountSq
        (mul_nonneg
          (mul_nonneg (by norm_num) (sub_nonneg.mpr hab))
          (Real.exp_nonneg _))
    _ = 4 * (b - a) * Real.exp (-2 * delta * a) *
          (C ^ 2 * Real.exp (2 * kappa * a)) := by
      rw [mul_pow, show Real.exp (kappa * a) ^ 2 =
          Real.exp (2 * kappa * a) by
        rw [pow_two, ← Real.exp_add]
        congr 1
        ring]
    _ = 4 * (b - a) * C ^ 2 *
          Real.exp (-2 * (delta - kappa) * a) := by
      calc
        4 * (b - a) * Real.exp (-2 * delta * a) *
              (C ^ 2 * Real.exp (2 * kappa * a)) =
            4 * (b - a) * C ^ 2 *
              (Real.exp (-2 * delta * a) *
                Real.exp (2 * kappa * a)) := by ring
        _ = _ := by
          rw [← Real.exp_add]
          congr 2
          ring

/-- Carlson controls the automatically separated left remainder on every
fixed logarithmic window. The top cluster is deliberately absent from this
bound and remains the next non-cancellation problem. -/
theorem
    eventually_integral_normSq_positiveZeroDensityLeftRemainder_le_of_carlson
    {rho0 : ℂ} {beta sigma tau eta delta L : ℝ}
    (hsigma : 1 / 2 < sigma)
    (hsigmaOne : sigma < 1)
    (htau : 0 < tau)
    (heta : 0 < eta)
    (hdelta : 0 ≤ delta)
    (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ᶠ a : ℝ in atTop,
        (∫ y in Icc a (a + L),
          Complex.normSq
            (normalizedPositiveZeroDensityContributionOn
              (positiveZeroDensityResidualLeftRemainder
                rho0 beta sigma (Real.exp (tau * a)) delta)
              beta y)) ≤
          4 * L * C ^ 2 *
            Real.exp
              (-2 *
                (delta -
                  (4 * sigma * (1 - sigma) * tau + eta)) * a) := by
  rcases eventually_zeroDensityCount_exp_height_le_of_carlson
      hsigma hsigmaOne htau heta with
    ⟨C, hC, hcount⟩
  refine ⟨C, hC, ?_⟩
  filter_upwards [hcount, eventually_ge_atTop (0 : ℝ)] with
    a hcountA ha
  have hbound :=
    integral_normSq_normalizedPositiveZeroDensityLeftRemainder_le_of_count_exp
      (rho0 := rho0) (beta := beta) (sigma := sigma)
      (T := Real.exp (tau * a)) (delta := delta)
      (a := a) (b := a + L) (C := C)
      (kappa := 4 * sigma * (1 - sigma) * tau + eta)
      hsigma.le hdelta ha (le_add_of_nonneg_right hL) hcountA
  simpa only [add_sub_cancel_left] using hbound

/-- The exact energy-transfer inequality for the cluster decomposition.
Consequently, a lower bound for the top-cluster energy transfers to the full
positive-height residual after subtracting the Carlson-controlled left
remainder. This theorem does not supply the cluster lower bound. -/
theorem integral_normSq_normalizedPositiveResidual_ge_half_cluster_sub_left
    (rho0 : ℂ) (beta sigma T delta a b : ℝ) :
    (1 / 2 : ℝ) *
        (∫ y in Icc a b,
          Complex.normSq
            (normalizedPositiveZeroDensityContributionOn
              (positiveZeroDensityResidualTopBandCluster
                rho0 beta sigma T delta) beta y)) -
      (∫ y in Icc a b,
        Complex.normSq
          (normalizedPositiveZeroDensityContributionOn
            (positiveZeroDensityResidualLeftRemainder
              rho0 beta sigma T delta) beta y)) ≤
    ∫ y in Icc a b,
      Complex.normSq
        (normalizedPositiveZeroDensityResidualContribution
          rho0 beta sigma T y) := by
  classical
  let cluster : ℝ → ℂ := fun y =>
    normalizedPositiveZeroDensityContributionOn
      (positiveZeroDensityResidualTopBandCluster
        rho0 beta sigma T delta) beta y
  let left : ℝ → ℂ := fun y =>
    normalizedPositiveZeroDensityContributionOn
      (positiveZeroDensityResidualLeftRemainder
        rho0 beta sigma T delta) beta y
  let residual : ℝ → ℂ := fun y =>
    normalizedPositiveZeroDensityResidualContribution
      rho0 beta sigma T y
  have hdecomp (y : ℝ) :
      residual y = cluster y + left y := by
    simpa only [residual, cluster, left] using
      normalizedPositiveZeroDensityResidualContribution_eq_cluster_add_left
        rho0 beta sigma T delta y
  have hclusterContinuous : Continuous cluster := by
    dsimp only [cluster, normalizedPositiveZeroDensityContributionOn]
    simp_rw [
      ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
        _ _ _ rfl]
    fun_prop
  have hleftContinuous : Continuous left := by
    dsimp only [left, normalizedPositiveZeroDensityContributionOn]
    simp_rw [
      ZeroForcedOscillation.realExp_cpow_eq_growth_mul_oscillation
        _ _ _ rfl]
    fun_prop
  have hresidualContinuous : Continuous residual := by
    exact (hclusterContinuous.add hleftContinuous).congr
      (fun y => (hdecomp y).symm)
  have hclusterIntegrable :
      IntegrableOn (fun y => Complex.normSq (cluster y)) (Icc a b) :=
    (Complex.continuous_normSq.comp hclusterContinuous).integrableOn_Icc
  have hleftIntegrable :
      IntegrableOn (fun y => Complex.normSq (left y)) (Icc a b) :=
    (Complex.continuous_normSq.comp hleftContinuous).integrableOn_Icc
  have hresidualIntegrable :
      IntegrableOn (fun y => Complex.normSq (residual y)) (Icc a b) :=
    (Complex.continuous_normSq.comp hresidualContinuous).integrableOn_Icc
  have hpoint (y : ℝ) :
      (1 / 2 : ℝ) * Complex.normSq (cluster y) -
          Complex.normSq (left y) ≤
        Complex.normSq (residual y) := by
    have htriangle :
        ‖cluster y‖ ≤ ‖residual y‖ + ‖left y‖ := by
      calc
        ‖cluster y‖ = ‖residual y - left y‖ := by
          rw [hdecomp]
          simp
        _ ≤ ‖residual y‖ + ‖left y‖ := norm_sub_le _ _
    have hsquare :
        ‖cluster y‖ ^ 2 ≤
          (‖residual y‖ + ‖left y‖) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) htriangle 2
    have hsumSquare :
        (‖residual y‖ + ‖left y‖) ^ 2 ≤
          2 * ‖residual y‖ ^ 2 + 2 * ‖left y‖ ^ 2 := by
      nlinarith [sq_nonneg (‖residual y‖ - ‖left y‖)]
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq,
      Complex.normSq_eq_norm_sq]
    nlinarith [hsquare.trans hsumSquare]
  have hleftSideIntegrable :
      IntegrableOn
        (fun y =>
          (1 / 2 : ℝ) * Complex.normSq (cluster y) -
            Complex.normSq (left y))
        (Icc a b) :=
    (hclusterIntegrable.const_mul (1 / 2 : ℝ)).sub hleftIntegrable
  have hmono :
      (∫ y in Icc a b,
          ((1 / 2 : ℝ) * Complex.normSq (cluster y) -
            Complex.normSq (left y))) ≤
        ∫ y in Icc a b, Complex.normSq (residual y) := by
    apply integral_mono_ae hleftSideIntegrable hresidualIntegrable
    exact Filter.Eventually.of_forall hpoint
  calc
    (1 / 2 : ℝ) *
          (∫ y in Icc a b, Complex.normSq (cluster y)) -
        (∫ y in Icc a b, Complex.normSq (left y)) =
      ∫ y in Icc a b,
        ((1 / 2 : ℝ) * Complex.normSq (cluster y) -
          Complex.normSq (left y)) := by
      rw [integral_sub
          (hclusterIntegrable.const_mul (1 / 2 : ℝ)) hleftIntegrable,
        integral_const_mul]
    _ ≤ ∫ y in Icc a b, Complex.normSq (residual y) := hmono

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
