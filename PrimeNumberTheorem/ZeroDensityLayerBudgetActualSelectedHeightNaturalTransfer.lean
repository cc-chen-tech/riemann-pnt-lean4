import PrimeNumberTheorem.ZeroDensityLayerBudgetActualSelectedHeightUnifiedTransfer

/-!
# Natural-point selected-height oscillation transfer

The available uniform good-height theorem controls the explicit-formula
remainder at natural evaluation points.  It does not provide a real-variable
`atTop` estimate.  This module records the exact transfer principle that this
input supports, without silently strengthening its domain.

The resulting lower transfer requires the visible main cluster to have
unbounded natural-point witnesses as well.  A merely real-variable witness is
not enough: sampling a small remainder only at integers cannot control the
remainder at an arbitrary real witness point.
-/

namespace PrimeNumberTheorem

open Filter Topology

/-- A natural-point remainder is negligible relative to a natural-point
amplitude when its normalized absolute value tends to zero. -/
def NaturalPointTargetAmplitudeNegligible
    (amplitude remainder : ℕ → ℝ) : Prop :=
  Tendsto
    (fun m : ℕ => |remainder m| / amplitude m)
    atTop (𝓝 0)

/-- An unsigned target-amplitude witness occurring at arbitrarily large
natural evaluation points. -/
def HasFarNaturalPointTargetAmplitudeWitness
    (f amplitude : ℕ → ℝ) : Prop :=
  ∀ M : ℕ, ∃ m : ℕ, M ≤ m ∧ amplitude m ≤ |f m|

/-- Real-variable target-amplitude negligibility remains valid after sampling
at natural points. -/
theorem TargetAmplitudeNegligible.naturalPoint
    {amplitude remainder : ℝ → ℝ}
    (hnegligible : TargetAmplitudeNegligible amplitude remainder) :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => amplitude (m : ℝ))
      (fun m : ℕ => remainder (m : ℝ)) := by
  unfold TargetAmplitudeNegligible at hnegligible
  unfold NaturalPointTargetAmplitudeNegligible
  change
    Tendsto
      ((fun x => |remainder x| / amplitude x) ∘
        fun m : ℕ => (m : ℝ))
      atTop (𝓝 0)
  exact hnegligible.comp tendsto_natCast_atTop_atTop

/-- Eventual positivity on the real ray remains valid at natural samples. -/
theorem eventually_naturalPoint_pos_of_eventually_pos
    {amplitude : ℝ → ℝ}
    (hamplitude : ∀ᶠ x : ℝ in atTop, 0 < amplitude x) :
    ∀ᶠ m : ℕ in atTop, 0 < amplitude (m : ℝ) :=
  tendsto_natCast_atTop_atTop.eventually hamplitude

/-- A normalized natural-point remainder is eventually smaller than every
positive fraction of the sampled target amplitude. -/
theorem eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
    {amplitude remainder : ℕ → ℝ}
    (hamplitude : ∀ᶠ m in atTop, 0 < amplitude m)
    (hnegligible :
      NaturalPointTargetAmplitudeNegligible amplitude remainder)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) :
    ∀ᶠ m in atTop, |remainder m| < epsilon * amplitude m := by
  have hratio :
      ∀ᶠ m in atTop, |remainder m| / amplitude m < epsilon :=
    (tendsto_order.mp hnegligible).2 epsilon hepsilon
  filter_upwards [hamplitude, hratio] with m hamplitudeM hratioM
  exact (div_lt_iff₀ hamplitudeM).mp hratioM

/-- Three natural-point normalized remainders have sum eventually smaller
than half the sampled target amplitude. -/
theorem
    eventually_abs_naturalPoint_three_remainders_lt_half
    {amplitude realAxis contour complement : ℕ → ℝ}
    (hamplitude : ∀ᶠ m in atTop, 0 < amplitude m)
    (hrealAxis :
      NaturalPointTargetAmplitudeNegligible amplitude realAxis)
    (hcontour :
      NaturalPointTargetAmplitudeNegligible amplitude contour)
    (hcomplement :
      NaturalPointTargetAmplitudeNegligible amplitude complement) :
    ∀ᶠ m in atTop,
      |realAxis m + contour m + complement m| < amplitude m / 2 := by
  have hrealAxisSmall :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hrealAxis (epsilon := (1 / 6 : ℝ)) (by norm_num)
  have hcontourSmall :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hcontour (epsilon := (1 / 6 : ℝ)) (by norm_num)
  have hcomplementSmall :=
    eventually_abs_lt_mul_of_naturalPointTargetAmplitudeNegligible
      hamplitude hcomplement (epsilon := (1 / 6 : ℝ)) (by norm_num)
  filter_upwards
      [hrealAxisSmall, hcontourSmall, hcomplementSmall] with
      m hrealAxisM hcontourM hcomplementM
  have htriangle :=
    abs_add_three (realAxis m) (contour m) (complement m)
  linarith

/-- Natural-point main witnesses survive three normalized natural-point
remainders at half the target amplitude. -/
theorem
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
    {amplitude main realAxis contour complement error : ℕ → ℝ}
    (hamplitude : ∀ᶠ m in atTop, 0 < amplitude m)
    (hrealAxis :
      NaturalPointTargetAmplitudeNegligible amplitude realAxis)
    (hcontour :
      NaturalPointTargetAmplitudeNegligible amplitude contour)
    (hcomplement :
      NaturalPointTargetAmplitudeNegligible amplitude complement)
    (hmain : HasFarNaturalPointTargetAmplitudeWitness main amplitude)
    (hdecomp :
      ∀ m : ℕ,
        error m = main m + (realAxis m + contour m + complement m)) :
    HasFarNaturalPointTargetAmplitudeWitness error
      (fun m => amplitude m / 2) := by
  have hsmall :=
    eventually_abs_naturalPoint_three_remainders_lt_half
      hamplitude hrealAxis hcontour hcomplement
  rw [eventually_atTop] at hsmall
  rcases hsmall with ⟨M₀, hM₀⟩
  intro M
  rcases hmain (max M M₀) with ⟨m, hm, hmainM⟩
  have hmM : M ≤ m := le_trans (le_max_left M M₀) hm
  have hmM₀ : M₀ ≤ m := le_trans (le_max_right M M₀) hm
  refine ⟨m, hmM, ?_⟩
  exact
    half_targetAmplitude_le_abs_error hmainM (hM₀ m hmM₀).le
      (hdecomp m)

/-- An unbounded natural-point witness embeds into the existing real-variable
far-witness interface. -/
theorem HasFarNaturalPointTargetAmplitudeWitness.toReal
    {f amplitude : ℝ → ℝ}
    (hwitness :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => f (m : ℝ))
        (fun m : ℕ => amplitude (m : ℝ))) :
    HasFarTargetAmplitudeWitness f amplitude := by
  intro X
  rcases exists_nat_ge X with ⟨M, hXM⟩
  rcases hwitness M with ⟨m, hmM, hm⟩
  have hcast : (M : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hmM
  exact ⟨(m : ℝ), hXM.trans hcast, hm⟩

/-- Natural-point certificate for the actual selected-height explicit-formula
remainder.  This is deliberately weaker than the real-variable certificate in
`ZeroDensityLayerBudgetActualSelectedHeightUnifiedTransfer`. -/
structure ActualSelectedHeightNaturalPointRemainderCertificate
    (beta : ℝ) (H : ℝ → ℝ) : Prop where
  negligible :
    NaturalPointTargetAmplitudeNegligible
      (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))
      (fun m : ℕ =>
        actualPNTExplicitFormulaRelativeRemainder H (m : ℝ))

/--
Actual selected-height lower transfer using only natural-point control of the
explicit-formula remainder.

The selected-height Carlson complement and closed real-axis term already have
real-variable normalized limits, so they can be sampled automatically.  The
main-cluster witness must occur at natural points because the contour input is
known only there.
-/
theorem
    actualSelectedHeight_naturalPointRemainder_lowerTransfer
    {beta alpha : ℝ} (hbeta : 0 < beta)
    {S : Finset ℂ} {n : ℕ} {H : ℝ → ℝ}
    {input :
      (x : ℝ) →
        PositiveZeroOutsideClusterBucketInput (H x) S n}
    (certificate :
      ActualCarlsonOutsideClusterGoodHeightFiniteStripCertificate
        beta alpha S n H input)
    (remainderCertificate :
      ActualSelectedHeightNaturalPointRemainderCertificate beta H)
    (hmain :
      HasFarNaturalPointTargetAmplitudeWitness
        (fun m : ℕ => dynamicVisibleClusterPNTMain H S (m : ℝ))
        (fun m : ℕ => targetZeroPowerAmplitude beta (m : ℝ))) :
    HasFarTargetAmplitudeWitness relativeChebyshevPsi0Error
      (fun x => targetZeroPowerAmplitude beta x / 2) := by
  apply HasFarNaturalPointTargetAmplitudeWitness.toReal
  apply
    hasFarNaturalPointTargetAmplitudeWitness_of_three_remainders
      (eventually_naturalPoint_pos_of_eventually_pos
        (targetZeroPowerAmplitude_eventually_pos beta))
      (actualPNTClosedRealAxisRelativeTerm_targetAmplitudeNegligible hbeta).naturalPoint
      remainderCertificate.negligible
      certificate.actualSignedComplementCertificate.complement_negligible.naturalPoint
      hmain
  intro m
  exact
    relativeChebyshevPsi0Error_eq_visibleCluster_add_actualResiduals
      H S (m : ℝ)

end PrimeNumberTheorem
