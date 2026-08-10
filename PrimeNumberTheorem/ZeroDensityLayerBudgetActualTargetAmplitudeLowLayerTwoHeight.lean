import PrimeNumberTheorem.ZeroDensityLayerBudgetPNTHybridActualLowLayerDecay
import PrimeNumberTheorem.ZeroDensityLayerBudgetCarlsonActualTwoHeightSplit

/-!
# Actual target-amplitude two-height split for the global low layer

The single-height global-zero-count estimate is incompatible with the
contour condition near the target-amplitude threshold.  This module splits an
actual outside-cluster bucket layer at an intermediate ordinate.  The low
piece is counted at the intermediate height, while the high annulus gains
that height in the zero-kernel denominator.
-/

open Complex Filter
open scoped BigOperators Topology

namespace PrimeNumberTheorem

/-- The part of an actual outside-cluster layer below an intermediate
ordinate. -/
noncomputable def positiveOutsideClusterLayerLowOrdinate
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) (U : ℝ) : Finset ℂ :=
  (input.layer i).filter fun rho => rho.im ≤ U

/-- The part of an actual outside-cluster layer above an intermediate
ordinate. -/
noncomputable def positiveOutsideClusterLayerHighAnnulus
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) (U : ℝ) : Finset ℂ :=
  (input.layer i).filter fun rho => U < rho.im

theorem positiveOutsideClusterLayer_eq_low_union_high
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) (U : ℝ) :
    input.layer i =
      positiveOutsideClusterLayerLowOrdinate input i U ∪
        positiveOutsideClusterLayerHighAnnulus input i U := by
  ext rho
  simp only [positiveOutsideClusterLayerLowOrdinate,
    positiveOutsideClusterLayerHighAnnulus, Finset.mem_union,
    Finset.mem_filter]
  constructor
  · intro hrho
    rcases le_or_gt rho.im U with hle | hgt
    · exact Or.inl ⟨hrho, hle⟩
    · exact Or.inr ⟨hrho, hgt⟩
  · rintro (⟨hrho, _⟩ | ⟨hrho, _⟩) <;> exact hrho

theorem positiveOutsideClusterLayerLowOrdinate_disjoint_high
    {T : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) (U : ℝ) :
    Disjoint
      (positiveOutsideClusterLayerLowOrdinate input i U)
      (positiveOutsideClusterLayerHighAnnulus input i U) := by
  rw [Finset.disjoint_left]
  intro rho hlow hhigh
  have hle : rho.im ≤ U := (Finset.mem_filter.mp hlow).2
  have hlt : U < rho.im := (Finset.mem_filter.mp hhigh).2
  exact (not_lt_of_ge hle) hlt

/-- The low-ordinate filtered layer is counted by global zero multiplicity at
the intermediate height. -/
theorem positiveOutsideClusterLayerLowOrdinate_multiplicityMass_le
    {T U : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) :
    analyticMultiplicityMass
        (positiveOutsideClusterLayerLowOrdinate input i U) ≤
      ExplicitFormulaAux.globalZeroMultiplicity U := by
  unfold analyticMultiplicityMass ExplicitFormulaAux.globalZeroMultiplicity
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    have hlayer := (Finset.mem_filter.mp hrho).1
    have himU := (Finset.mem_filter.mp hrho).2
    have houtside :
        rho ∈ positiveNontrivialZerosOutsideClusterFinset T S :=
      (Finset.mem_filter.mp hlayer).1
    have hmem :=
      mem_positiveNontrivialZerosOutsideClusterFinset.mp houtside
    rw [mem_nontrivialZerosFinset]
    refine ⟨hmem.1, ?_⟩
    rw [abs_of_pos hmem.2.1]
    exact himU
  · intro rho _ _
    exact
      (Nat.cast_nonneg (analyticOrderNatAt riemannZeta rho) :
        (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta rho : ℝ))

/-- The high annulus remains counted by global zero multiplicity at the
outer height. -/
theorem positiveOutsideClusterLayerHighAnnulus_multiplicityMass_le
    {T U : ℝ} {S : Finset ℂ} {n : ℕ}
    (input : PositiveZeroOutsideClusterBucketInput T S n)
    (i : Fin n) :
    analyticMultiplicityMass
        (positiveOutsideClusterLayerHighAnnulus input i U) ≤
      ExplicitFormulaAux.globalZeroMultiplicity T := by
  unfold analyticMultiplicityMass ExplicitFormulaAux.globalZeroMultiplicity
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro rho hrho
    have hlayer := (Finset.mem_filter.mp hrho).1
    have houtside :
        rho ∈ positiveNontrivialZerosOutsideClusterFinset T S :=
      (Finset.mem_filter.mp hlayer).1
    have hmem :=
      mem_positiveNontrivialZerosOutsideClusterFinset.mp houtside
    rw [mem_nontrivialZerosFinset]
    refine ⟨hmem.1, ?_⟩
    rw [abs_of_pos hmem.2.1]
    exact hmem.2.2.1
  · intro rho _ _
    exact
      (Nat.cast_nonneg (analyticOrderNatAt riemannZeta rho) :
        (0 : ℝ) ≤ (analyticOrderNatAt riemannZeta rho : ℝ))

/-- Multiplicity-weighted kernel mass of the low-ordinate piece. -/
noncomputable def dynamicOutsideClusterLowOrdinateMass
    {n : ℕ} (T U : ℝ → ℝ) (S : Finset ℂ)
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (x : ℝ) : ℝ :=
  ∑ rho ∈ positiveOutsideClusterLayerLowOrdinate
      (input x) i (U x),
    ‖pntRelativeZeroContribution x rho‖

/-- Multiplicity-weighted kernel mass of the high-ordinate annulus. -/
noncomputable def dynamicOutsideClusterHighAnnulusMass
    {n : ℕ} (T U : ℝ → ℝ) (S : Finset ℂ)
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (x : ℝ) : ℝ :=
  ∑ rho ∈ positiveOutsideClusterLayerHighAnnulus
      (input x) i (U x),
    ‖pntRelativeZeroContribution x rho‖

/-- The complete layer mass is exactly the sum of its two ordinate pieces. -/
theorem dynamicOutsideClusterLayerMass_eq_low_add_high
    {n : ℕ} (T U : ℝ → ℝ) (S : Finset ℂ)
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (x : ℝ) :
    (∑ rho ∈ (input x).layer i,
        ‖pntRelativeZeroContribution x rho‖) =
      dynamicOutsideClusterLowOrdinateMass T U S input i x +
        dynamicOutsideClusterHighAnnulusMass T U S input i x := by
  rw [positiveOutsideClusterLayer_eq_low_union_high
      (input x) i (U x),
    Finset.sum_union
      (positiveOutsideClusterLayerLowOrdinate_disjoint_high
        (input x) i (U x))]
  rfl

theorem dynamicOutsideClusterLowOrdinateMass_le
    {n : ℕ} {T U : ℝ → ℝ} {S : Finset ℂ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (tau kappa : ℝ)
    (hkappa : 0 < kappa)
    (hnorm : ∀ x rho, rho ∈ (input x).layer i → kappa ≤ ‖rho‖)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ tau)
    {x : ℝ} (hx : 1 ≤ x) :
    dynamicOutsideClusterLowOrdinateMass T U S input i x ≤
      stripEndpointRelativeKernelBudget kappa tau x *
        ExplicitFormulaAux.globalZeroMultiplicity (U x) := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · exact
      stripEndpointRelativeKernelBudget_nonneg
        (zero_le_one.trans hx) hkappa.le
  · intro rho hrho
    have hlayer := (Finset.mem_filter.mp hrho).1
    exact norm_pntRelativeSimpleZeroKernel_le_stripEndpoint
      hx hkappa (hnorm x rho hlayer) (hre x rho hlayer)
  · exact
      positiveOutsideClusterLayerLowOrdinate_multiplicityMass_le
        (input x) i

theorem dynamicOutsideClusterHighAnnulusMass_le
    {n : ℕ} {T U : ℝ → ℝ} {S : Finset ℂ}
    (input : (x : ℝ) → PositiveZeroOutsideClusterBucketInput (T x) S n)
    (i : Fin n) (tau : ℝ)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ tau)
    {x : ℝ} (hx : 1 ≤ x) (hU : 0 < U x) :
    dynamicOutsideClusterHighAnnulusMass T U S input i x ≤
      (x ^ (tau - 1) / U x) *
        ExplicitFormulaAux.globalZeroMultiplicity (T x) := by
  apply sum_norm_pntRelativeZeroContribution_le_kernel_mul_of_mass_le
  · exact div_nonneg (Real.rpow_nonneg (by positivity) _) hU.le
  · intro rho hrho
    have hlayer := (Finset.mem_filter.mp hrho).1
    have hfloor : U x ≤ rho.im :=
      le_of_lt (Finset.mem_filter.mp hrho).2
    exact norm_pntRelativeSimpleZeroKernel_le_rectangle
      hx hU hfloor (hre x rho hlayer)
  · exact
      positiveOutsideClusterLayerHighAnnulus_multiplicityMass_le
        (input x) i

theorem polynomial_highAnnulusKernel_eq_shiftedEndpoint
    {x tau gamma : ℝ} (hx : 0 < x) :
    x ^ (tau - 1) / carlsonPolynomialHeight gamma x =
      stripEndpointRelativeKernelBudget 1 (tau - gamma) x := by
  unfold carlsonPolynomialHeight stripEndpointRelativeKernelBudget
  rw [← Real.rpow_sub hx]
  congr 1
  ring

/-- A global coefficient simultaneously controls both actual pieces. -/
theorem exists_globalCoefficient_dynamicOutsideClusterTwoHeightMass_le
    {n : ℕ} {S : Finset ℂ} {beta tau alpha gamma kappa : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n)
    (hkappa : 0 < kappa)
    (hnorm : ∀ x rho, rho ∈ (input x).layer i → kappa ≤ ‖rho‖)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ tau) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, 1 ≤ x →
        4 ≤ carlsonPolynomialHeight gamma x →
        4 ≤ carlsonPolynomialHeight alpha x →
        dynamicOutsideClusterLowOrdinateMass
            (carlsonPolynomialHeight alpha)
            (carlsonPolynomialHeight gamma) S input i x /
            targetZeroPowerAmplitude beta x ≤
          actualHybridGlobalLowLayerMajorant C
              (carlsonPolynomialHeight gamma x) kappa tau x /
            targetZeroPowerAmplitude beta x ∧
        dynamicOutsideClusterHighAnnulusMass
            (carlsonPolynomialHeight alpha)
            (carlsonPolynomialHeight gamma) S input i x /
            targetZeroPowerAmplitude beta x ≤
          actualHybridGlobalLowLayerMajorant C
              (carlsonPolynomialHeight alpha x) 1
              (tau - gamma) x /
            targetZeroPowerAmplitude beta x := by
  rcases ExplicitFormulaAux.exists_globalZeroMultiplicity_le_mul_log with
    ⟨C, hC, hglobal⟩
  refine ⟨C, hC, ?_⟩
  intro x hx hinner houter
  have hx0 : 0 < x := zero_lt_one.trans_le hx
  have hamp : 0 < targetZeroPowerAmplitude beta x :=
    Real.rpow_pos_of_pos hx0 _
  constructor
  · apply (div_le_div_iff_of_pos_right hamp).2
    calc
      dynamicOutsideClusterLowOrdinateMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S input i x ≤
        stripEndpointRelativeKernelBudget kappa tau x *
          ExplicitFormulaAux.globalZeroMultiplicity
            (carlsonPolynomialHeight gamma x) :=
        dynamicOutsideClusterLowOrdinateMass_le
          input i tau kappa hkappa hnorm hre hx
      _ ≤ stripEndpointRelativeKernelBudget kappa tau x *
          (C * carlsonPolynomialHeight gamma x *
            (1 + Real.log
              (carlsonPolynomialHeight gamma x + 6))) :=
        mul_le_mul_of_nonneg_left (hglobal _ hinner)
          (stripEndpointRelativeKernelBudget_nonneg
            (zero_le_one.trans hx) hkappa.le)
      _ = actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight gamma x) kappa tau x := by
        unfold actualHybridGlobalLowLayerMajorant
        ring
  · apply (div_le_div_iff_of_pos_right hamp).2
    calc
      dynamicOutsideClusterHighAnnulusMass
          (carlsonPolynomialHeight alpha)
          (carlsonPolynomialHeight gamma) S input i x ≤
        (x ^ (tau - 1) /
            carlsonPolynomialHeight gamma x) *
          ExplicitFormulaAux.globalZeroMultiplicity
            (carlsonPolynomialHeight alpha x) :=
        dynamicOutsideClusterHighAnnulusMass_le
          input i tau hre hx (Real.rpow_pos_of_pos hx0 _)
      _ ≤ (x ^ (tau - 1) /
            carlsonPolynomialHeight gamma x) *
          (C * carlsonPolynomialHeight alpha x *
            (1 + Real.log
              (carlsonPolynomialHeight alpha x + 6))) :=
        mul_le_mul_of_nonneg_left (hglobal _ houter)
          (div_nonneg (Real.rpow_nonneg hx0.le _)
            (Real.rpow_nonneg hx0.le _))
      _ = actualHybridGlobalLowLayerMajorant C
          (carlsonPolynomialHeight alpha x) 1
          (tau - gamma) x := by
        rw [polynomial_highAnnulusKernel_eq_shiftedEndpoint hx0]
        unfold actualHybridGlobalLowLayerMajorant
        ring

/-- The existing logarithmic majorant tends to zero after target
normalization whenever its polynomial exponent has a strict margin. -/
theorem tendsto_actualHybridGlobalLowLayerMajorant_div_target
    {C kappa beta tau alpha epsilon : ℝ}
    (hC : 0 ≤ C) (hkappa : 0 < kappa)
    (halpha : 0 < alpha) (hepsilon : 0 < epsilon)
    (hmargin : tau - beta + alpha + epsilon < 0) :
    Tendsto
      (fun x =>
        actualHybridGlobalLowLayerMajorant C
            (carlsonPolynomialHeight alpha x) kappa tau x /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  have hlog :=
    eventually_one_add_log_polynomialHeight_add_six_le_log_four halpha
  have hlimit :=
    tendsto_actualHybridLowNormalizedLogPowerMajorant_zero
      hC hkappa halpha hepsilon hmargin
  refine squeeze_zero' ?_ ?_ hlimit
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [actualHybridGlobalLowLayerMajorant_div_target_eq
      (zero_lt_one.trans_le hx)]
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    have hlog0 : 0 ≤ Real.log (x ^ alpha + 6) :=
      Real.log_nonneg (by
        have hrpow : 0 ≤ x ^ alpha := Real.rpow_nonneg hx0.le _
        linarith)
    exact
      mul_nonneg
        (mul_nonneg
          (mul_nonneg hC (inv_nonneg.mpr hkappa.le))
          (Real.rpow_nonneg hx0.le _))
        (add_nonneg zero_le_one hlog0)
  · filter_upwards [eventually_ge_atTop (1 : ℝ), hlog] with x hx hlogx
    have hx0 : 0 < x := zero_lt_one.trans_le hx
    rw [actualHybridGlobalLowLayerMajorant_div_target_eq hx0]
    calc
      C * kappa⁻¹ * x ^ (tau - beta + alpha) *
          (1 + Real.log (x ^ alpha + 6)) ≤
        C * kappa⁻¹ * x ^ (tau - beta + alpha) *
          ((alpha + 2) * Real.log x ^ 4) :=
        mul_le_mul_of_nonneg_left hlogx
          (mul_nonneg
            (mul_nonneg hC (inv_nonneg.mpr hkappa.le))
            (Real.rpow_nonneg hx0.le _))
      _ = actualHybridLowNormalizedLogPowerMajorant
          C kappa beta tau alpha x := by
        unfold actualHybridLowNormalizedLogPowerMajorant
        ring

/-- Both actual ordinate pieces, and hence their total multiplicity-weighted
mass, are negligible on the target-zero scale. -/
theorem tendsto_dynamicOutsideClusterTwoHeightMass_div_target
    {n : ℕ} {S : Finset ℂ}
    {beta tau alpha gamma kappa epsilon : ℝ}
    (input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput
          (carlsonPolynomialHeight alpha x) S n)
    (i : Fin n)
    (hkappa : 0 < kappa)
    (hnorm : ∀ x rho, rho ∈ (input x).layer i → kappa ≤ ‖rho‖)
    (hre : ∀ x rho, rho ∈ (input x).layer i → rho.re ≤ tau)
    (halpha : 0 < alpha) (hgamma : 0 < gamma)
    (hepsilon : 0 < epsilon)
    (hlow : gamma + tau - beta + epsilon < 0)
    (hhigh : alpha + tau - beta - gamma + epsilon < 0) :
    Tendsto
      (fun x =>
        (dynamicOutsideClusterLowOrdinateMass
            (carlsonPolynomialHeight alpha)
            (carlsonPolynomialHeight gamma) S input i x +
          dynamicOutsideClusterHighAnnulusMass
            (carlsonPolynomialHeight alpha)
            (carlsonPolynomialHeight gamma) S input i x) /
          targetZeroPowerAmplitude beta x)
      atTop (nhds 0) := by
  rcases
      exists_globalCoefficient_dynamicOutsideClusterTwoHeightMass_le
        (beta := beta) (alpha := alpha) (gamma := gamma)
        input i hkappa hnorm hre with
    ⟨C, hC, hpointwise⟩
  have hinnerHeight := tendsto_rpow_atTop hgamma
  have houterHeight := tendsto_rpow_atTop halpha
  have hlowLimit :=
    tendsto_actualHybridGlobalLowLayerMajorant_div_target
      (C := C) (kappa := kappa) (beta := beta)
      (tau := tau) (alpha := gamma) (epsilon := epsilon)
      hC hkappa hgamma hepsilon (by linarith)
  have hhighLimit :=
    tendsto_actualHybridGlobalLowLayerMajorant_div_target
      (C := C) (kappa := 1) (beta := beta)
      (tau := tau - gamma) (alpha := alpha) (epsilon := epsilon)
      hC (by norm_num : (0 : ℝ) < 1) halpha hepsilon (by linarith)
  have hmajor :
      Tendsto
        (fun x =>
          actualHybridGlobalLowLayerMajorant C
              (carlsonPolynomialHeight gamma x) kappa tau x /
              targetZeroPowerAmplitude beta x +
            actualHybridGlobalLowLayerMajorant C
              (carlsonPolynomialHeight alpha x) 1
              (tau - gamma) x /
              targetZeroPowerAmplitude beta x)
        atTop (nhds 0) := by
    simpa using hlowLimit.add hhighLimit
  refine squeeze_zero' ?_ ?_ hmajor
  · filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    exact div_nonneg
      (add_nonneg
        (Finset.sum_nonneg fun _ _ => norm_nonneg _)
        (Finset.sum_nonneg fun _ _ => norm_nonneg _))
      (Real.rpow_nonneg (zero_le_one.trans hx) _)
  · filter_upwards
      [eventually_ge_atTop (1 : ℝ),
        hinnerHeight.eventually (eventually_ge_atTop 4),
        houterHeight.eventually (eventually_ge_atTop 4)]
      with x hx hinner houter
    have hp := hpointwise x hx hinner houter
    rw [add_div]
    exact add_le_add hp.1 hp.2

/-- At the balanced cut `gamma = alpha / 2`, both target-normalized
polynomial exponents coincide. -/
theorem lowLayerTwoHeight_balanced_exponents
    (beta tau alpha : ℝ) :
    alpha / 2 + tau - beta =
        (alpha / 2) + tau - beta ∧
      alpha + tau - beta - alpha / 2 =
        alpha / 2 + tau - beta := by
  constructor <;> ring

/-- A contour-compatible balanced outer height exists exactly below the
low-layer threshold. -/
theorem exists_lowLayerTwoHeight_strictMargins
    {beta tau : ℝ}
    (hbetaOne : beta < 1)
    (htau : tau < (3 * beta - 1) / 2) :
    ∃ alpha gamma epsilon : ℝ,
      1 - beta < alpha ∧
      0 < gamma ∧ gamma ≤ alpha ∧
      0 < epsilon ∧
      gamma + tau - beta + epsilon < 0 ∧
      alpha + tau - beta - gamma + epsilon < 0 := by
  let upper := 2 * (beta - tau)
  have hgap : 1 - beta < upper := by
    dsimp [upper]
    linarith
  let alpha := ((1 - beta) + upper) / 2
  have hcontour : 1 - beta < alpha := by
    dsimp [alpha]
    linarith
  have halphaUpper : alpha < upper := by
    dsimp [alpha]
    linarith
  have halpha : 0 < alpha :=
    (sub_pos.mpr hbetaOne).trans hcontour
  let gamma := alpha / 2
  have hgamma : 0 < gamma := by
    dsimp [gamma]
    linarith
  have hgammaAlpha : gamma ≤ alpha := by
    dsimp [gamma]
    linarith
  have hcommon : gamma + tau - beta < 0 := by
    dsimp [gamma, upper] at *
    linarith
  let epsilon := -(gamma + tau - beta) / 2
  have hepsilon : 0 < epsilon := by
    dsimp [epsilon]
    linarith
  have hlow : gamma + tau - beta + epsilon < 0 := by
    dsimp [epsilon]
    linarith
  have hhigh :
      alpha + tau - beta - gamma + epsilon < 0 := by
    dsimp [gamma] at *
    linarith
  exact
    ⟨alpha, gamma, epsilon, hcontour, hgamma, hgammaAlpha,
      hepsilon, hlow, hhigh⟩

/-- The interval of usable low-layer endpoints is nonempty exactly in the
range needed by the previous Carlson strip stack. -/
theorem exists_lowLayerTwoHeight_parameters_of_twoThirds
    {beta : ℝ} (hbeta : 2 / 3 < beta) (hbetaOne : beta < 1) :
    ∃ tau alpha gamma epsilon : ℝ,
      1 / 2 < tau ∧
      tau < (3 * beta - 1) / 2 ∧
      1 - beta < alpha ∧
      0 < gamma ∧ gamma ≤ alpha ∧
      0 < epsilon ∧
      gamma + tau - beta + epsilon < 0 ∧
      alpha + tau - beta - gamma + epsilon < 0 := by
  let threshold := (3 * beta - 1) / 2
  have hhalf : 1 / 2 < threshold := by
    dsimp [threshold]
    linarith
  let tau := (1 / 2 + threshold) / 2
  have htauHalf : 1 / 2 < tau := by
    dsimp [tau]
    linarith
  have htauThreshold : tau < threshold := by
    dsimp [tau]
    linarith
  rcases exists_lowLayerTwoHeight_strictMargins
      hbetaOne (by simpa [threshold] using htauThreshold) with
    ⟨alpha, gamma, epsilon, hcontour, hgamma,
      hgammaAlpha, hepsilon, hlow, hhigh⟩
  exact
    ⟨tau, alpha, gamma, epsilon, htauHalf,
      by simpa [threshold] using htauThreshold,
      hcontour, hgamma, hgammaAlpha, hepsilon, hlow, hhigh⟩

end PrimeNumberTheorem
