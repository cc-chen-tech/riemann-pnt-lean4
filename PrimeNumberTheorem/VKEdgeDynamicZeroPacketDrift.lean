import PrimeNumberTheorem.VKEdgeDynamicZeroPacket

open Complex
open MeasureTheory Set
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Real-part drift for dynamic zeta-zero packets

This module compares the actual normalized contribution of the finite-height
complementary zeta packets with the exponential sum obtained by freezing every
real part at the logarithmic center `a`.  The comparison is pointwise on the
forward window and keeps the real-part band loss explicit.
-/

/-- The actual moving contribution of the inspected complementary zeta
packets.  The coefficient records analytic multiplicity and the value frozen
at `a`; the drift restores the true real part at `y`. -/
noncomputable def dynamicComplementMovingPacketContribution
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (y : ℝ) : ℂ :=
  MathlibAux.driftingExponentialPolynomial
    (dynamicComplementPacketIndexSet S T K)
    (fun z => finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2)
    (fun z => z.2.im)
    (fun z => z.2.re - beta)
    a y

/-- The same actual packet collection with its real-part growth frozen at the
logarithmic center `a`. -/
noncomputable def dynamicComplementFrozenPacketContribution
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (y : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (dynamicComplementPacketIndexSet S T K)
    (fun z => finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2)
    (fun z => z.2.im)
    y

/-- Gaussian energy of the actual moving complementary packet collection on
the forward centered window `[0, L]`. -/
noncomputable def dynamicComplementForwardMovingGaussianSecondMoment
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
    (m L : ℝ) : ℝ :=
  ∫ t : ℝ in Set.Icc 0 L,
    normalizedGaussian m t *
      ‖dynamicComplementMovingPacketContribution
        S T beta a K (a + t)‖ ^ 2

/-- On a forward logarithmic window, zeros in the real-part band
`[beta - delta, beta]` differ from their frozen packet model by the explicit
drift factor `1 - exp (-delta * (y - a))`. -/
theorem norm_dynamicComplementMovingPacketContribution_sub_frozen_le
    {S : Finset ℂ} {T beta a delta y : ℝ} {K : Finset ℕ}
    (hdelta : 0 ≤ delta)
    (hay : a ≤ y)
    (hband : ∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
      beta - delta ≤ rho.re ∧ rho.re ≤ beta) :
    ‖dynamicComplementMovingPacketContribution S T beta a K y -
        dynamicComplementFrozenPacketContribution S T beta a K y‖ ≤
      (1 - Real.exp (-delta * (y - a))) *
        ∑ n ∈ K, dynamicComplementPacketCoefficientMass S T beta a n := by
  classical
  let I := dynamicComplementPacketIndexSet S T K
  let coeff : (Σ _n : ℕ, ℂ) → ℂ := fun z =>
    finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2
  let freq : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.im
  let drift : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.re - beta
  have hdrift : ∀ z ∈ I, -delta ≤ drift z ∧ drift z ≤ 0 := by
    intro z hz
    have hz' :
        z.1 ∈ K ∧ z.2 ∈ dynamicComplementZeroPacket S T z.1 := by
      simpa [I, dynamicComplementPacketIndexSet] using
        (Finset.mem_sigma.mp hz)
    have hb := hband z.1 hz'.1 z.2 hz'.2
    dsimp [drift]
    constructor <;> linarith
  have hmass :
      (∑ z ∈ I, ‖coeff z‖) =
        ∑ n ∈ K, dynamicComplementPacketCoefficientMass S T beta a n := by
    dsimp [I, coeff, dynamicComplementPacketIndexSet,
      dynamicComplementPacketCoefficientMass]
    rw [Finset.sum_sigma]
  have h :=
    MathlibAux.norm_driftingExponentialPolynomial_sub_exponentialPolynomial_le
      (S := I) (coeff := coeff) (freq := freq) (drift := drift)
      hdelta hay hdrift
  rw [hmass] at h
  simpa [dynamicComplementMovingPacketContribution,
    dynamicComplementFrozenPacketContribution, I, coeff, freq, drift] using h

private theorem dynamicComplementFrozenPacketContribution_centered
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (t : ℝ) :
    dynamicComplementFrozenPacketContribution S T beta a K (a + t) =
      DirichletPolynomial.finiteExponentialSum
        (dynamicComplementPacketIndexSet S T K)
        (DirichletPolynomial.phaseTwist
          (fun z => finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta a z.2)
        (fun z => z.2.im) a)
        (fun z => z.2.im) t := by
  classical
  change
    DirichletPolynomial.finiteExponentialSum
        (dynamicComplementPacketIndexSet S T K)
        (fun z => finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2)
        (fun z => z.2.im) (a + t) =
      _
  exact
    (finiteExponentialSum_phaseTwist_eq_shift
      (dynamicComplementPacketIndexSet S T K)
      (fun z => finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta a z.2)
      (fun z => z.2.im) a t).symm

private theorem norm_finiteExponentialSum_le_sum_norm
    {ι : Type*} [DecidableEq ι]
    (I₀ : Finset ι) (c : ι → ℂ) (omega : ι → ℝ) (t : ℝ) :
    ‖DirichletPolynomial.finiteExponentialSum I₀ c omega t‖ ≤
      ∑ i ∈ I₀, ‖c i‖ := by
  unfold DirichletPolynomial.finiteExponentialSum
  calc
    ‖∑ i ∈ I₀, c i * Complex.exp (Complex.I * (omega i * t))‖ ≤
        ∑ i ∈ I₀,
          ‖c i * Complex.exp (Complex.I * (omega i * t))‖ :=
      norm_sum_le _ _
    _ = ∑ i ∈ I₀, ‖c i‖ := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_mul, Complex.norm_exp]
      simp

private theorem integrable_centeredFrozenGaussianIntegrand
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
    {m : ℝ} (hm : 0 < m) :
    Integrable (fun t : ℝ =>
      normalizedGaussian m t *
        ‖dynamicComplementFrozenPacketContribution
          S T beta a K (a + t)‖ ^ 2) := by
  classical
  let mass : ℝ :=
    ∑ n ∈ K, dynamicComplementPacketCoefficientMass S T beta a n
  have hmajor :
      Integrable (fun t : ℝ => normalizedGaussian m t * mass ^ 2) :=
    by
      simpa [mul_comm] using
        (integrable_normalizedGaussian hm).const_mul (mass ^ 2)
  apply hmajor.mono'
  · have hweight : Continuous (normalizedGaussian m) :=
      continuous_iff_continuousAt.mpr fun t =>
        (hasDerivAt_normalizedGaussian hm t).continuousAt
    have hfrozen : Continuous (fun t : ℝ =>
        dynamicComplementFrozenPacketContribution
          S T beta a K (a + t)) := by
      unfold dynamicComplementFrozenPacketContribution
        MathlibAux.exponentialPolynomial
      fun_prop
    exact (hweight.mul (hfrozen.norm.pow 2)).aestronglyMeasurable
  filter_upwards with t
  have hsum :
      ‖dynamicComplementFrozenPacketContribution S T beta a K (a + t)‖ ≤
        mass := by
    have h :=
      norm_finiteExponentialSum_le_sum_norm
        (dynamicComplementPacketIndexSet S T K)
        (fun z => finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2)
        (fun z => z.2.im) (a + t)
    change
      ‖DirichletPolynomial.finiteExponentialSum
        (dynamicComplementPacketIndexSet S T K)
        (fun z => finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2)
        (fun z => z.2.im) (a + t)‖ ≤ mass
    calc
      _ ≤ ∑ z ∈ dynamicComplementPacketIndexSet S T K,
          ‖finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta a z.2‖ := h
      _ = mass := by
        dsimp [mass, dynamicComplementPacketIndexSet,
          dynamicComplementPacketCoefficientMass]
        rw [Finset.sum_sigma]
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    apply Finset.sum_nonneg
    intro n hn
    unfold dynamicComplementPacketCoefficientMass
    positivity
  have hsquare :
      ‖dynamicComplementFrozenPacketContribution
          S T beta a K (a + t)‖ ^ 2 ≤ mass ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hsum 2
  rw [Real.norm_eq_abs, abs_of_nonneg
    (mul_nonneg (normalizedGaussian_pos hm t).le (sq_nonneg _))]
  exact mul_le_mul_of_nonneg_left hsquare
    (normalizedGaussian_pos hm t).le

/-- On a forward centered Gaussian window, the actual moving packet energy is
bounded by twice the centered frozen energy plus the explicit real-part drift
loss.  No separation of ordinates is required. -/
theorem dynamicComplementForwardMovingGaussianSecondMoment_le_centeredFrozen
    {S : Finset ℂ} {T beta a m L delta : ℝ} {K : Finset ℕ}
    (hm : 0 < m)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hband : ∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
      beta - delta ≤ rho.re ∧ rho.re ≤ beta) :
    dynamicComplementForwardMovingGaussianSecondMoment
        S T beta a K m L ≤
      2 * dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m +
        2 * (1 - Real.exp (-delta * L)) ^ 2 *
          (∑ n ∈ K,
            dynamicComplementPacketCoefficientMass S T beta a n) ^ 2 := by
  classical
  let moving : ℝ → ℂ := fun t =>
    dynamicComplementMovingPacketContribution S T beta a K (a + t)
  let frozen : ℝ → ℂ := fun t =>
    dynamicComplementFrozenPacketContribution S T beta a K (a + t)
  let weight : ℝ → ℝ := normalizedGaussian m
  let mass : ℝ :=
    ∑ n ∈ K, dynamicComplementPacketCoefficientMass S T beta a n
  let q : ℝ := 1 - Real.exp (-delta * L)
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hmovingContinuous : Continuous moving := by
    dsimp [moving, dynamicComplementMovingPacketContribution,
      MathlibAux.driftingExponentialPolynomial]
    fun_prop
  have hfrozenContinuous : Continuous frozen := by
    dsimp [frozen, dynamicComplementFrozenPacketContribution,
      MathlibAux.exponentialPolynomial]
    fun_prop
  have hq : 0 ≤ q := by
    dsimp [q]
    exact sub_nonneg.mpr
      (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hdelta) hL))
  have hmass : 0 ≤ mass := by
    dsimp [mass]
    apply Finset.sum_nonneg
    intro n hn
    unfold dynamicComplementPacketCoefficientMass
    positivity
  have hclose (t : ℝ) (ht : t ∈ Set.Icc 0 L) :
      ‖moving t - frozen t‖ ≤ q * mass := by
    have hpoint :=
      norm_dynamicComplementMovingPacketContribution_sub_frozen_le
        (S := S) (T := T) (beta := beta) (a := a)
        (delta := delta) (y := a + t) (K := K)
        hdelta (by linarith [ht.1]) hband
    have hqt :
        1 - Real.exp (-delta * ((a + t) - a)) ≤ q := by
      have hexp :
          Real.exp (-delta * L) ≤ Real.exp (-delta * t) := by
        apply Real.exp_le_exp.mpr
        exact mul_le_mul_of_nonpos_left ht.2 (neg_nonpos.mpr hdelta)
      dsimp [q]
      convert (sub_le_sub_left hexp 1) using 1 <;> ring
    exact hpoint.trans
      (mul_le_mul_of_nonneg_right hqt hmass)
  have hpoint (t : ℝ) (ht : t ∈ Set.Icc 0 L) :
      weight t * ‖moving t‖ ^ 2 ≤
        weight t *
          (2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2) := by
    have htriangle :
        ‖moving t‖ ≤ ‖frozen t‖ + q * mass := by
      calc
        ‖moving t‖ =
            ‖(moving t - frozen t) + frozen t‖ := by ring_nf
        _ ≤ ‖moving t - frozen t‖ + ‖frozen t‖ := norm_add_le _ _
        _ ≤ q * mass + ‖frozen t‖ :=
          add_le_add_left (hclose t ht) _
        _ = ‖frozen t‖ + q * mass := by ring
    have hsquare :
        ‖moving t‖ ^ 2 ≤
          2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2 := by
      nlinarith [norm_nonneg (moving t), norm_nonneg (frozen t),
        mul_nonneg hq hmass,
        sq_nonneg (‖frozen t‖ - q * mass)]
    exact mul_le_mul_of_nonneg_left hsquare
      (normalizedGaussian_pos hm t).le
  have hmovingInt :
      IntegrableOn (fun t => weight t * ‖moving t‖ ^ 2)
        (Set.Icc 0 L) := by
    exact (hweightContinuous.mul
      (hmovingContinuous.norm.pow 2)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hfrozenInt :
      IntegrableOn (fun t => weight t * ‖frozen t‖ ^ 2)
        (Set.Icc 0 L) := by
    exact (hweightContinuous.mul
      (hfrozenContinuous.norm.pow 2)).continuousOn.integrableOn_compact
        isCompact_Icc
  have hconstInt :
      IntegrableOn (fun t => weight t * (q * mass) ^ 2)
        (Set.Icc 0 L) := by
    simpa [weight, mul_comm] using
      ((integrable_normalizedGaussian hm).const_mul
        ((q * mass) ^ 2)).integrableOn
  have hupperInt :
      IntegrableOn
        (fun t => weight t *
          (2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2))
        (Set.Icc 0 L) := by
    have hinside : Continuous (fun t : ℝ =>
        2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2) :=
      (continuous_const.mul (hfrozenContinuous.norm.pow 2)).add
        continuous_const
    exact (hweightContinuous.mul hinside).continuousOn.integrableOn_compact
      isCompact_Icc
  have hmono :
      (∫ t : ℝ in Set.Icc 0 L, weight t * ‖moving t‖ ^ 2) ≤
        ∫ t : ℝ in Set.Icc 0 L,
          weight t *
            (2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2) :=
    setIntegral_mono_on hmovingInt hupperInt measurableSet_Icc hpoint
  have hsplit :
      (∫ t : ℝ in Set.Icc 0 L,
          weight t *
            (2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2)) =
        2 * (∫ t : ℝ in Set.Icc 0 L,
          weight t * ‖frozen t‖ ^ 2) +
        2 * (q * mass) ^ 2 *
          (∫ t : ℝ in Set.Icc 0 L, weight t) := by
    calc
      (∫ t : ℝ in Set.Icc 0 L,
          weight t *
            (2 * ‖frozen t‖ ^ 2 + 2 * (q * mass) ^ 2)) =
          ∫ t : ℝ in Set.Icc 0 L,
            (2 * (weight t * ‖frozen t‖ ^ 2) +
              2 * (weight t * (q * mass) ^ 2)) := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        ring
      _ =
          (∫ t : ℝ in Set.Icc 0 L,
            2 * (weight t * ‖frozen t‖ ^ 2)) +
          ∫ t : ℝ in Set.Icc 0 L,
            2 * (weight t * (q * mass) ^ 2) :=
        MeasureTheory.integral_add
          (hfrozenInt.const_mul 2) (hconstInt.const_mul 2)
      _ =
          2 * (∫ t : ℝ in Set.Icc 0 L,
            weight t * ‖frozen t‖ ^ 2) +
          2 * (q * mass) ^ 2 *
            (∫ t : ℝ in Set.Icc 0 L, weight t) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_const_mul,
          MeasureTheory.integral_mul_const]
        ring
  have hweightMass :
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤ 1 := by
    calc
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤ ∫ t : ℝ, weight t :=
        setIntegral_le_integral (integrable_normalizedGaussian hm)
          (Filter.Eventually.of_forall fun t =>
            (normalizedGaussian_pos hm t).le)
      _ = 1 := integral_normalizedGaussian hm
  have hfrozenGlobal :
      Integrable (fun t : ℝ => weight t * ‖frozen t‖ ^ 2) := by
    simpa [weight, frozen] using
      integrable_centeredFrozenGaussianIntegrand S T beta a K hm
  have hfrozenSet :
      (∫ t : ℝ in Set.Icc 0 L, weight t * ‖frozen t‖ ^ 2) ≤
        dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m := by
    calc
      (∫ t : ℝ in Set.Icc 0 L, weight t * ‖frozen t‖ ^ 2) ≤
          ∫ t : ℝ, weight t * ‖frozen t‖ ^ 2 :=
        setIntegral_le_integral hfrozenGlobal
          (Filter.Eventually.of_forall fun t =>
            mul_nonneg (normalizedGaussian_pos hm t).le (sq_nonneg _))
      _ = dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m := by
        unfold dynamicComplementCenteredFrozenGaussianSecondMoment
        apply MeasureTheory.integral_congr_ae
        filter_upwards with t
        dsimp [weight, frozen]
        rw [dynamicComplementFrozenPacketContribution_centered]
  rw [hsplit] at hmono
  dsimp [dynamicComplementForwardMovingGaussianSecondMoment,
    moving, frozen, weight, q, mass] at hmono ⊢
  nlinarith [hfrozenSet, hweightMass, sq_nonneg (q * mass)]

/-- A genuinely large Gaussian `L²` contribution from the actual moving
finite-height complement forces a new nonempty packet of actual zeta zeros.
The displayed drift budget is proved above; it is not an external
small-complement assumption. -/
theorem exists_absorbableDynamicComplementPacket_of_forwardMovingGaussianL2_gt
    {S : Finset ℂ} {T beta a eta m L delta : ℝ} {K : Finset ℕ}
    (heta : 0 < eta)
    (hm : 1 ≤ m)
    (hL : 0 ≤ L)
    (hdelta : 0 ≤ delta)
    (hK : K.Nonempty)
    (hband : ∀ n ∈ K, ∀ rho ∈ dynamicComplementZeroPacket S T n,
      beta - delta ≤ rho.re ∧ rho.re ≤ beta)
    (hlarge :
      2 * eta +
          2 * (1 - Real.exp (-delta * L)) ^ 2 *
            (∑ n ∈ K,
              dynamicComplementPacketCoefficientMass S T beta a n) ^ 2 <
        dynamicComplementForwardMovingGaussianSecondMoment
          S T beta a K m L) :
    ∃ n ∈ K,
      eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
        (dynamicComplementZeroPacket S T n).Nonempty ∧
          Disjoint S (dynamicComplementZeroPacket S T n) ∧
            dynamicComplementZeroPacket S T n ⊆
              nontrivialZerosFinset T ∧
              S.card < (S ∪ dynamicComplementZeroPacket S T n).card := by
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hupper :=
    dynamicComplementForwardMovingGaussianSecondMoment_le_centeredFrozen
      (S := S) (T := T) (beta := beta) (a := a) (m := m)
      (L := L) (delta := delta) (K := K)
      hm0 hL hdelta hband
  have henergy :
      eta <
        dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m := by
    nlinarith
  exact
    exists_absorbableDynamicComplementPacket_of_centeredFrozenGaussianL2_gt
      heta hm hK henergy

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
