import PrimeNumberTheorem.VKEdgeDynamicZeroPacketDrift
import PrimeNumberTheorem.ZeroForcedOscillationComplementaryBound

open Complex MeasureTheory Set

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Dynamic maximal real-part layers

For a finite height truncation and a current absorbed zero set `S`, this
module selects the maximal real part among the remaining zeros.  It then
constructs the positive finite-height gap below that layer and proves that
the half-gap real band contains exactly the maximal layer.  Consequently the
outside-band packet contains only zeros with a uniform negative real-part
drift; no more-right zero is hidden in the remainder.
-/

/-- Nontrivial height-`T` zeros not yet absorbed into `S`. -/
noncomputable def dynamicComplementZeroSet
    (S : Finset ℂ) (T : ℝ) : Finset ℂ :=
  nontrivialZerosFinset T \ S

/-- Maximal real part among the remaining height-`T` zeros, with total default
value `0` when the complement is empty. -/
noncomputable def dynamicMaximalComplementRealPart
    (S : Finset ℂ) (T : ℝ) : ℝ :=
  if h : (dynamicComplementZeroSet S T).Nonempty then
    (dynamicComplementZeroSet S T).sup' h Complex.re
  else
    0

/-- Remaining zeros on the selected maximal-real-part layer. -/
noncomputable def dynamicMaximalRealPartZeroLayer
    (S : Finset ℂ) (T : ℝ) : Finset ℂ := by
  classical
  exact (dynamicComplementZeroSet S T).filter
    (fun rho => rho.re = dynamicMaximalComplementRealPart S T)

/-- Remaining zeros strictly below the selected maximal-real-part layer. -/
noncomputable def dynamicBelowMaximalRealPartZeroSet
    (S : Finset ℂ) (T : ℝ) : Finset ℂ := by
  classical
  exact (dynamicComplementZeroSet S T).filter
    (fun rho => rho.re ≠ dynamicMaximalComplementRealPart S T)

/-- Positive gap from the selected maximal layer to the next lower remaining
real part.  If there is no lower layer, the total default value is `1`. -/
noncomputable def dynamicMaximalComplementRealPartGap
    (S : Finset ℂ) (T : ℝ) : ℝ :=
  if h : (dynamicBelowMaximalRealPartZeroSet S T).Nonempty then
    dynamicMaximalComplementRealPart S T -
      (dynamicBelowMaximalRealPartZeroSet S T).sup' h Complex.re
  else
    1

/-- Half of the positive finite-height gap.  This is the band width used to
separate the maximal layer from every lower layer. -/
noncomputable def dynamicMaximalComplementBandWidth
    (S : Finset ℂ) (T : ℝ) : ℝ :=
  dynamicMaximalComplementRealPartGap S T / 2

/-- Every remaining zero lies at or to the left of the selected maximal real
part. -/
theorem re_le_dynamicMaximalComplementRealPart
    {S : Finset ℂ} {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ dynamicComplementZeroSet S T) :
    rho.re ≤ dynamicMaximalComplementRealPart S T := by
  classical
  have hC : (dynamicComplementZeroSet S T).Nonempty := ⟨rho, hrho⟩
  rw [dynamicMaximalComplementRealPart, dif_pos hC]
  exact Finset.le_sup' Complex.re hrho

/-- Membership in the selected maximal layer is exactly complement membership
together with equality to the selected real part. -/
theorem mem_dynamicMaximalRealPartZeroLayer
    {S : Finset ℂ} {T : ℝ} {rho : ℂ} :
    rho ∈ dynamicMaximalRealPartZeroLayer S T ↔
      rho ∈ dynamicComplementZeroSet S T ∧
        rho.re = dynamicMaximalComplementRealPart S T := by
  classical
  simp [dynamicMaximalRealPartZeroLayer]

/-- A nonempty dynamic complement has a nonempty selected maximal layer. -/
theorem dynamicMaximalRealPartZeroLayer_nonempty
    (S : Finset ℂ) (T : ℝ)
    (hC : (dynamicComplementZeroSet S T).Nonempty) :
    (dynamicMaximalRealPartZeroLayer S T).Nonempty := by
  classical
  rcases Finset.exists_mem_eq_sup' hC Complex.re with ⟨rho, hrho, hre⟩
  refine ⟨rho, mem_dynamicMaximalRealPartZeroLayer.mpr ⟨hrho, ?_⟩⟩
  rw [dynamicMaximalComplementRealPart, dif_pos hC, hre]

/-- Membership below the maximal layer records complement membership and
strict inequality of real parts. -/
theorem mem_dynamicBelowMaximalRealPartZeroSet
    {S : Finset ℂ} {T : ℝ} {rho : ℂ} :
    rho ∈ dynamicBelowMaximalRealPartZeroSet S T ↔
      rho ∈ dynamicComplementZeroSet S T ∧
        rho.re < dynamicMaximalComplementRealPart S T := by
  classical
  rw [dynamicBelowMaximalRealPartZeroSet, Finset.mem_filter]
  constructor
  · rintro ⟨hrho, hne⟩
    exact ⟨hrho, lt_of_le_of_ne
      (re_le_dynamicMaximalComplementRealPart hrho) hne⟩
  · rintro ⟨hrho, hlt⟩
    exact ⟨hrho, ne_of_lt hlt⟩

/-- The finite-height gap below the dynamic maximal layer is always positive. -/
theorem dynamicMaximalComplementRealPartGap_pos
    (S : Finset ℂ) (T : ℝ) :
    0 < dynamicMaximalComplementRealPartGap S T := by
  classical
  by_cases hbelow :
      (dynamicBelowMaximalRealPartZeroSet S T).Nonempty
  · rw [dynamicMaximalComplementRealPartGap, dif_pos hbelow]
    exact sub_pos.mpr
      ((Finset.sup'_lt_iff hbelow).mpr fun rho hrho =>
        (mem_dynamicBelowMaximalRealPartZeroSet.mp hrho).2)
  · simp [dynamicMaximalComplementRealPartGap, hbelow]

/-- Every remaining zero below the maximal layer lies at least the selected
gap to its left. -/
theorem re_le_dynamicMaximalComplementRealPart_sub_gap
    {S : Finset ℂ} {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ dynamicBelowMaximalRealPartZeroSet S T) :
    rho.re ≤
      dynamicMaximalComplementRealPart S T -
        dynamicMaximalComplementRealPartGap S T := by
  classical
  have hbelow :
      (dynamicBelowMaximalRealPartZeroSet S T).Nonempty :=
    ⟨rho, hrho⟩
  rw [dynamicMaximalComplementRealPartGap, dif_pos hbelow]
  have hsup :=
    Finset.le_sup' Complex.re hrho
  linarith

/-- The half-gap band width is strictly positive. -/
theorem dynamicMaximalComplementBandWidth_pos
    (S : Finset ℂ) (T : ℝ) :
    0 < dynamicMaximalComplementBandWidth S T := by
  unfold dynamicMaximalComplementBandWidth
  positivity [dynamicMaximalComplementRealPartGap_pos S T]

/-- Among remaining height-`T` zeros, the half-gap real band contains exactly
the selected maximal-real-part layer. -/
theorem dynamicComplementRealBand_iff_re_eq_dynamicMaximal
    {S : Finset ℂ} {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ dynamicComplementZeroSet S T) :
    dynamicComplementRealBand
        (dynamicMaximalComplementRealPart S T)
        (dynamicMaximalComplementBandWidth S T) rho ↔
      rho.re = dynamicMaximalComplementRealPart S T := by
  constructor
  · intro hband
    apply le_antisymm
    · exact re_le_dynamicMaximalComplementRealPart hrho
    · by_contra hnot
      have hlt :
          rho.re < dynamicMaximalComplementRealPart S T :=
        lt_of_not_ge hnot
      have hbelow :
          rho ∈ dynamicBelowMaximalRealPartZeroSet S T :=
        mem_dynamicBelowMaximalRealPartZeroSet.mpr ⟨hrho, hlt⟩
      have hgap :=
        re_le_dynamicMaximalComplementRealPart_sub_gap hbelow
      have hgapPos :=
        dynamicMaximalComplementRealPartGap_pos S T
      have hbandLower := hband.1
      unfold dynamicMaximalComplementBandWidth at hbandLower
      linarith
  · intro hre
    constructor
    · rw [hre]
      have hwidth :=
        (dynamicMaximalComplementBandWidth_pos S T).le
      linarith
    · exact hre.le

/-- A zero outside the half-gap band is necessarily on a lower real-part
layer; no more-right zero remains after dynamic maximal-layer selection. -/
theorem re_le_dynamicMaximal_sub_gap_of_not_realBand
    {S : Finset ℂ} {T : ℝ} {rho : ℂ}
    (hrho : rho ∈ dynamicComplementZeroSet S T)
    (hout :
      ¬ dynamicComplementRealBand
        (dynamicMaximalComplementRealPart S T)
        (dynamicMaximalComplementBandWidth S T) rho) :
    rho.re ≤
      dynamicMaximalComplementRealPart S T -
        dynamicMaximalComplementRealPartGap S T := by
  have hne :
      rho.re ≠ dynamicMaximalComplementRealPart S T := by
    intro hre
    exact hout
      ((dynamicComplementRealBand_iff_re_eq_dynamicMaximal hrho).mpr hre)
  have hlt :
      rho.re < dynamicMaximalComplementRealPart S T :=
    lt_of_le_of_ne
      (re_le_dynamicMaximalComplementRealPart hrho) hne
  exact re_le_dynamicMaximalComplementRealPart_sub_gap
    (mem_dynamicBelowMaximalRealPartZeroSet.mpr ⟨hrho, hlt⟩)

/-- Every outside-band zero in an inspected dynamic packet has a uniform
negative drift at least the full finite-height gap. -/
theorem re_le_dynamicMaximal_sub_gap_of_mem_outsidePacket
    {S : Finset ℂ} {T : ℝ} {n : ℕ} {rho : ℂ}
    (hrho :
      rho ∈ dynamicComplementOutsideRealBandZeroPacket
        S T
        (dynamicMaximalComplementRealPart S T)
        (dynamicMaximalComplementBandWidth S T) n) :
    rho.re ≤
      dynamicMaximalComplementRealPart S T -
        dynamicMaximalComplementRealPartGap S T := by
  classical
  rcases Finset.mem_filter.mp hrho with ⟨hrhoPacket, hout⟩
  have hrhoComplement :
      rho ∈ dynamicComplementZeroSet S T := by
    change
      rho ∈ zeroOrdinateUnitBucket n ∩
        (nontrivialZerosFinset T \ S) at hrhoPacket
    rcases Finset.mem_inter.mp hrhoPacket with ⟨_, hrhoComplement⟩
    exact hrhoComplement
  exact re_le_dynamicMaximal_sub_gap_of_not_realBand hrhoComplement hout

/-- Total frozen coefficient mass of the inspected packet outside the
dynamic maximal-real-part half-gap band. -/
noncomputable def dynamicMaximalOutsidePacketCoefficientMass
    (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ) : ℝ :=
  ∑ z ∈ dynamicComplementOutsideRealBandPacketIndexSet
      S T
      (dynamicMaximalComplementRealPart S T)
      (dynamicMaximalComplementBandWidth S T) K,
    ‖finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta)
      (dynamicMaximalComplementRealPart S T) a z.2‖

/-- Raw reciprocal-norm multiplicity mass of the inspected packet outside
the dynamic maximal-real-part half-gap band. -/
noncomputable def dynamicMaximalOutsideReciprocalMultiplicityMass
    (S : Finset ℂ) (T : ℝ) (K : Finset ℕ) : ℝ :=
  ∑ z ∈ dynamicComplementOutsideRealBandPacketIndexSet
      S T
      (dynamicMaximalComplementRealPart S T)
      (dynamicMaximalComplementBandWidth S T) K,
    (analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖

/-- On a forward centered window, the inspected packet below the dynamic
maximal layer decays pointwise by at least the full finite-height real-part
gap. -/
theorem norm_dynamicMaximalOutsideMovingPacketContribution_le
    {S : Finset ℂ} {T a t : ℝ} {K : Finset ℕ}
    (ht : 0 ≤ t) :
    ‖dynamicComplementOutsideRealBandMovingPacketContribution
        S T
        (dynamicMaximalComplementRealPart S T) a
        (dynamicMaximalComplementBandWidth S T) K (a + t)‖ ≤
      Real.exp (-dynamicMaximalComplementRealPartGap S T * t) *
        dynamicMaximalOutsidePacketCoefficientMass S T a K := by
  classical
  let beta := dynamicMaximalComplementRealPart S T
  let gap := dynamicMaximalComplementRealPartGap S T
  let delta := dynamicMaximalComplementBandWidth S T
  let I₀ :=
    dynamicComplementOutsideRealBandPacketIndexSet S T beta delta K
  let coeff : (Σ _n : ℕ, ℂ) → ℂ := fun z =>
    finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2
  let freq : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.im
  let drift : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.re - beta
  have hdrift : ∀ z ∈ I₀, drift z ≤ -gap := by
    intro z hz
    have hz' :
        z.1 ∈ K ∧
          z.2 ∈ dynamicComplementOutsideRealBandZeroPacket
            S T beta delta z.1 := by
      simpa [I₀,
        dynamicComplementOutsideRealBandPacketIndexSet] using
          (Finset.mem_sigma.mp hz)
    have hre :
        z.2.re ≤
          dynamicMaximalComplementRealPart S T -
            dynamicMaximalComplementRealPartGap S T := by
      simpa [beta, gap, delta] using
        (re_le_dynamicMaximal_sub_gap_of_mem_outsidePacket hz'.2)
    dsimp [drift, beta, gap]
    linarith
  have hterm (z : Σ _n : ℕ, ℂ) (hz : z ∈ I₀) :
      ‖coeff z * (Real.exp (drift z * t) : ℂ) *
          Complex.exp (I * (freq z * (a + t)))‖ ≤
        Real.exp (-gap * t) * ‖coeff z‖ := by
    have hexp :
        Real.exp (drift z * t) ≤ Real.exp (-gap * t) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right (hdrift z hz) ht
    have hosc :
        ‖Complex.exp (I * (freq z * (a + t)))‖ = 1 := by
      rw [norm_exp]
      simp
    calc
      ‖coeff z * (Real.exp (drift z * t) : ℂ) *
          Complex.exp (I * (freq z * (a + t)))‖ =
          ‖coeff z‖ * Real.exp (drift z * t) := by
        rw [norm_mul, norm_mul, norm_real, Real.norm_eq_abs,
          abs_of_pos (Real.exp_pos _), hosc, mul_one]
      _ ≤ ‖coeff z‖ * Real.exp (-gap * t) :=
        mul_le_mul_of_nonneg_left hexp (norm_nonneg _)
      _ = Real.exp (-gap * t) * ‖coeff z‖ := by ring
  have hsum :
    ‖∑ z ∈ I₀,
        coeff z * (Real.exp (drift z * t) : ℂ) *
          Complex.exp (I * (freq z * (a + t)))‖ ≤
      Real.exp (-gap * t) * ∑ z ∈ I₀, ‖coeff z‖ := by
    calc
      ‖∑ z ∈ I₀,
          coeff z * (Real.exp (drift z * t) : ℂ) *
            Complex.exp (I * (freq z * (a + t)))‖ ≤
          ∑ z ∈ I₀,
            ‖coeff z * (Real.exp (drift z * t) : ℂ) *
              Complex.exp (I * (freq z * (a + t)))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ z ∈ I₀, Real.exp (-gap * t) * ‖coeff z‖ :=
        Finset.sum_le_sum fun z hz => hterm z hz
      _ = Real.exp (-gap * t) * ∑ z ∈ I₀, ‖coeff z‖ := by
        rw [Finset.mul_sum]
  simpa [dynamicComplementOutsideRealBandMovingPacketContribution,
    MathlibAux.driftingExponentialPolynomial,
    dynamicMaximalOutsidePacketCoefficientMass,
    I₀, coeff, freq, drift, beta, gap, delta,
    add_sub_cancel_left] using hsum

/-- At a nonnegative logarithmic center, the frozen coefficient mass below
the dynamic maximal layer gains the full finite-height gap factor
`exp (-gap * a)`. -/
theorem dynamicMaximalOutsidePacketCoefficientMass_le_exp_gap_mul_reciprocal
    (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ)
    (ha : 0 ≤ a) :
    dynamicMaximalOutsidePacketCoefficientMass S T a K ≤
      Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
        dynamicMaximalOutsideReciprocalMultiplicityMass S T K := by
  classical
  let beta := dynamicMaximalComplementRealPart S T
  let gap := dynamicMaximalComplementRealPartGap S T
  let delta := dynamicMaximalComplementBandWidth S T
  let I₀ :=
    dynamicComplementOutsideRealBandPacketIndexSet S T beta delta K
  have hterm (z : Σ _n : ℕ, ℂ) (hz : z ∈ I₀) :
      ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2‖ ≤
        Real.exp (-gap * a) *
          ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) := by
    have hz' :
        z.1 ∈ K ∧
          z.2 ∈ dynamicComplementOutsideRealBandZeroPacket
            S T beta delta z.1 := by
      simpa [I₀,
        dynamicComplementOutsideRealBandPacketIndexSet] using
          (Finset.mem_sigma.mp hz)
    have hre :
        z.2.re ≤ beta - gap := by
      simpa [beta, gap, delta] using
        (re_le_dynamicMaximal_sub_gap_of_mem_outsidePacket hz'.2)
    have hexp :
        Real.exp ((z.2.re - beta) * a) ≤ Real.exp (-gap * a) := by
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_right
      · linarith
      · exact ha
    have hraw :
        0 ≤ (analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖ := by
      positivity
    have hcoeffNorm :
        ‖finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta a z.2‖ =
          ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) *
            Real.exp ((z.2.re - beta) * a) := by
      unfold finiteZeroClusterCoefficientAt
      rw [norm_mul, norm_mul, norm_inv, norm_real, Real.norm_eq_abs,
        abs_of_pos (Real.exp_pos _)]
      simp only [Complex.norm_natCast]
      ring
    calc
      ‖finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2‖ =
          ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) *
            Real.exp ((z.2.re - beta) * a) := hcoeffNorm
      _ ≤ ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) *
            Real.exp (-gap * a) :=
        mul_le_mul_of_nonneg_left hexp hraw
      _ = Real.exp (-gap * a) *
          ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) := by
        ring
  calc
    dynamicMaximalOutsidePacketCoefficientMass S T a K =
        ∑ z ∈ I₀,
          ‖finiteZeroClusterCoefficientAt
            (analyticOrderNatAt riemannZeta) beta a z.2‖ := by
      rfl
    _ ≤ ∑ z ∈ I₀,
        Real.exp (-gap * a) *
          ((analyticOrderNatAt riemannZeta z.2 : ℝ) / ‖z.2‖) :=
      Finset.sum_le_sum fun z hz => hterm z hz
    _ = Real.exp (-gap * a) *
        dynamicMaximalOutsideReciprocalMultiplicityMass S T K := by
      rw [← Finset.mul_sum]
      rfl

/-- The raw outside-band mass is at most `K.card` copies of the full
height-`T` reciprocal-zero mass.  This deliberately avoids assuming that the
chosen bucket family has already been proved duplicate-free. -/
theorem
    dynamicMaximalOutsideReciprocalMultiplicityMass_le_card_mul_global
    (S : Finset ℂ) (T : ℝ) (K : Finset ℕ) :
    dynamicMaximalOutsideReciprocalMultiplicityMass S T K ≤
      (K.card : ℝ) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
  classical
  let beta := dynamicMaximalComplementRealPart S T
  let delta := dynamicMaximalComplementBandWidth S T
  have hpacket (n : ℕ) :
      ∑ rho ∈ dynamicComplementOutsideRealBandZeroPacket
          S T beta delta n,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ ≤
        ∑ rho ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun rho _ _ =>
      div_nonneg (Nat.cast_nonneg _) (norm_nonneg rho)
    intro rho hrho
    rcases Finset.mem_filter.mp hrho with ⟨hrhoPacket, _⟩
    change
      rho ∈ zeroOrdinateUnitBucket n ∩
        (nontrivialZerosFinset T \ S) at hrhoPacket
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hrhoPacket).2).1
  calc
    dynamicMaximalOutsideReciprocalMultiplicityMass S T K =
        ∑ n ∈ K,
          ∑ rho ∈ dynamicComplementOutsideRealBandZeroPacket
              S T beta delta n,
            (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ := by
      unfold dynamicMaximalOutsideReciprocalMultiplicityMass
        dynamicComplementOutsideRealBandPacketIndexSet
      rw [Finset.sum_sigma]
    _ ≤ ∑ _n ∈ K,
        ∑ rho ∈ nontrivialZerosFinset T,
          (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖ :=
      Finset.sum_le_sum fun n _ => hpacket n
    _ = (K.card : ℝ) *
        ExplicitFormulaAux.globalReciprocalZeroMultiplicity T := by
      simp [ExplicitFormulaAux.globalReciprocalZeroMultiplicity]

/-- The forward Gaussian energy of the packet below the dynamic maximal layer
is bounded by the square of its frozen center coefficient mass.  The
pointwise exponential gap decay is retained in the preceding theorem; this
corollary integrates it using only the unit mass of the normalized Gaussian.
-/
theorem
    dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_coefficientMass_sq
    (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ)
    {m L : ℝ} (hm : 0 < m) :
    dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
        S T
        (dynamicMaximalComplementRealPart S T) a
        (dynamicMaximalComplementBandWidth S T) K m L ≤
      dynamicMaximalOutsidePacketCoefficientMass S T a K ^ 2 := by
  let weight : ℝ → ℝ := normalizedGaussian m
  let moving : ℝ → ℂ := fun t =>
    dynamicComplementOutsideRealBandMovingPacketContribution
      S T
      (dynamicMaximalComplementRealPart S T) a
      (dynamicMaximalComplementBandWidth S T) K (a + t)
  let mass := dynamicMaximalOutsidePacketCoefficientMass S T a K
  have hmass : 0 ≤ mass := by
    dsimp [mass, dynamicMaximalOutsidePacketCoefficientMass]
    positivity
  have hweightContinuous : Continuous weight := by
    dsimp [weight]
    exact continuous_iff_continuousAt.mpr fun t =>
      (hasDerivAt_normalizedGaussian hm t).continuousAt
  have hmovingContinuous : Continuous moving := by
    dsimp [moving,
      dynamicComplementOutsideRealBandMovingPacketContribution,
      MathlibAux.driftingExponentialPolynomial]
    fun_prop
  have hmovingInt :
      IntegrableOn (fun t : ℝ => weight t * ‖moving t‖ ^ 2)
        (Set.Icc 0 L) :=
    (hweightContinuous.mul (hmovingContinuous.norm.pow 2)).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hmassInt :
      IntegrableOn (fun t : ℝ => weight t * mass ^ 2)
        (Set.Icc 0 L) :=
    (hweightContinuous.mul continuous_const).continuousOn
      |>.integrableOn_compact isCompact_Icc
  have hpoint :
      ∀ t ∈ Set.Icc (0 : ℝ) L,
        weight t * ‖moving t‖ ^ 2 ≤ weight t * mass ^ 2 := by
    intro t ht
    have hnorm :
        ‖moving t‖ ≤
          Real.exp (-dynamicMaximalComplementRealPartGap S T * t) *
            mass := by
      simpa [moving, mass] using
        (norm_dynamicMaximalOutsideMovingPacketContribution_le
          (S := S) (T := T) (a := a) (K := K) ht.1)
    have hdecay :
        Real.exp (-dynamicMaximalComplementRealPartGap S T * t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr
          (dynamicMaximalComplementRealPartGap_pos S T).le)
        ht.1
    have hnormMass : ‖moving t‖ ≤ mass :=
      hnorm.trans <| by
        calc
          Real.exp (-dynamicMaximalComplementRealPartGap S T * t) *
              mass ≤
              1 * mass :=
            mul_le_mul_of_nonneg_right hdecay hmass
          _ = mass := one_mul mass
    have hsquare : ‖moving t‖ ^ 2 ≤ mass ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hnormMass 2
    exact mul_le_mul_of_nonneg_left hsquare
      (normalizedGaussian_pos hm t).le
  have hmono :
      (∫ t : ℝ in Set.Icc 0 L, weight t * ‖moving t‖ ^ 2) ≤
        ∫ t : ℝ in Set.Icc 0 L, weight t * mass ^ 2 :=
    setIntegral_mono_on hmovingInt hmassInt measurableSet_Icc hpoint
  have hweightMass :
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤ 1 := by
    calc
      (∫ t : ℝ in Set.Icc 0 L, weight t) ≤ ∫ t : ℝ, weight t :=
        setIntegral_le_integral (integrable_normalizedGaussian hm)
          (Filter.Eventually.of_forall fun t =>
            (normalizedGaussian_pos hm t).le)
      _ = 1 := integral_normalizedGaussian hm
  calc
    dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
        S T
        (dynamicMaximalComplementRealPart S T) a
        (dynamicMaximalComplementBandWidth S T) K m L =
        ∫ t : ℝ in Set.Icc 0 L, weight t * ‖moving t‖ ^ 2 := by
      rfl
    _ ≤ ∫ t : ℝ in Set.Icc 0 L, weight t * mass ^ 2 := hmono
    _ = (∫ t : ℝ in Set.Icc 0 L, weight t) * mass ^ 2 := by
      rw [MeasureTheory.integral_mul_const]
    _ ≤ 1 * mass ^ 2 :=
      mul_le_mul_of_nonneg_right hweightMass (sq_nonneg mass)
    _ = dynamicMaximalOutsidePacketCoefficientMass S T a K ^ 2 := by
      simp [mass]

/-- Quantitative low-real-layer energy bound: at a nonnegative logarithmic
center, the outside-band Gaussian energy is suppressed by the square of the
full dynamic real-part gap. -/
theorem
    dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_exp_gap_sq
    (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ)
    {m L : ℝ} (hm : 0 < m) (ha : 0 ≤ a) :
    dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
        S T
        (dynamicMaximalComplementRealPart S T) a
        (dynamicMaximalComplementBandWidth S T) K m L ≤
      (Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
        dynamicMaximalOutsideReciprocalMultiplicityMass S T K) ^ 2 := by
  calc
    dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
        S T
        (dynamicMaximalComplementRealPart S T) a
        (dynamicMaximalComplementBandWidth S T) K m L ≤
      dynamicMaximalOutsidePacketCoefficientMass S T a K ^ 2 :=
        dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_coefficientMass_sq
          S T a K hm
    _ ≤
      (Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
        dynamicMaximalOutsideReciprocalMultiplicityMass S T K) ^ 2 :=
      pow_le_pow_left₀
        (by
          unfold dynamicMaximalOutsidePacketCoefficientMass
          positivity)
        (dynamicMaximalOutsidePacketCoefficientMass_le_exp_gap_mul_reciprocal
          S T a K ha)
        2

/-- Uniform quantitative form of the low-real-layer energy estimate.  The
repository's global reciprocal-zero `O(log^2 T)` bound pays for the inspected
bucket family, while the dynamic real-part gap supplies exponential decay in
the logarithmic center. -/
theorem
    exists_dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_log_sq
    :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : Finset ℂ) (T a : ℝ) (K : Finset ℕ) {m L : ℝ},
        4 ≤ T →
        0 ≤ a →
        0 < m →
        dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
            S T
            (dynamicMaximalComplementRealPart S T) a
            (dynamicMaximalComplementBandWidth S T) K m L ≤
          (Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
            ((K.card : ℝ) *
              (C * (1 + Real.log (T + 6)) ^ 2))) ^ 2 := by
  rcases ExplicitFormulaAux.exists_globalReciprocalZeroMultiplicity_le_log_sq
      with ⟨C, hC, hCbound⟩
  refine ⟨C, hC, ?_⟩
  intro S T a K m L hT ha hm
  have hraw :
      dynamicMaximalOutsideReciprocalMultiplicityMass S T K ≤
        (K.card : ℝ) * (C * (1 + Real.log (T + 6)) ^ 2) := by
    calc
      dynamicMaximalOutsideReciprocalMultiplicityMass S T K ≤
          (K.card : ℝ) *
            ExplicitFormulaAux.globalReciprocalZeroMultiplicity T :=
        dynamicMaximalOutsideReciprocalMultiplicityMass_le_card_mul_global
          S T K
      _ ≤ (K.card : ℝ) * (C * (1 + Real.log (T + 6)) ^ 2) :=
        mul_le_mul_of_nonneg_left (hCbound T hT) (Nat.cast_nonneg K.card)
  have hscaled :
      Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
          dynamicMaximalOutsideReciprocalMultiplicityMass S T K ≤
        Real.exp (-dynamicMaximalComplementRealPartGap S T * a) *
          ((K.card : ℝ) * (C * (1 + Real.log (T + 6)) ^ 2)) :=
    mul_le_mul_of_nonneg_left hraw (Real.exp_nonneg _)
  exact
    (dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_exp_gap_sq
      S T a K hm ha).trans
        (pow_le_pow_left₀
          (mul_nonneg (Real.exp_nonneg _)
            (by
              unfold dynamicMaximalOutsideReciprocalMultiplicityMass
              positivity))
          hscaled 2)

/-- Dynamic maximal-layer absorption with the outside-band energy fully paid
by the finite-height gap and the global reciprocal-zero `O(log^2 T)` bound.
The remaining substantive input is a lower bound for the full moving
complementary energy above the displayed explicit budget. -/
theorem
    exists_uniformDynamicMaximalLayerAbsorption_of_fullMovingGaussianL2_gt
    :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {S : Finset ℂ} {T a eta m L : ℝ} {K : Finset ℕ},
        4 ≤ T →
        0 ≤ a →
        0 < eta →
        1 ≤ m →
        0 ≤ L →
        K.Nonempty →
        2 *
            (2 * eta +
              2 *
                (1 - Real.exp
                  (-dynamicMaximalComplementBandWidth S T * L)) ^ 2 *
                (∑ n ∈ K,
                  dynamicComplementRealBandPacketCoefficientMass
                    S T
                    (dynamicMaximalComplementRealPart S T) a
                    (dynamicMaximalComplementBandWidth S T) n) ^ 2) +
            2 *
              (Real.exp
                  (-dynamicMaximalComplementRealPartGap S T * a) *
                ((K.card : ℝ) *
                  (C * (1 + Real.log (T + 6)) ^ 2))) ^ 2 <
          dynamicComplementForwardMovingGaussianSecondMoment
            S T (dynamicMaximalComplementRealPart S T) a K m L →
        ∃ n ∈ K,
          eta / (MathlibAux.gaussianBucketSchurConstant * K.card) <
              dynamicComplementRealBandPacketCoefficientMass
                S T
                (dynamicMaximalComplementRealPart S T) a
                (dynamicMaximalComplementBandWidth S T) n ^ 2 ∧
            (dynamicComplementRealBandZeroPacket
              S T
              (dynamicMaximalComplementRealPart S T)
              (dynamicMaximalComplementBandWidth S T) n).Nonempty ∧
              Disjoint S
                (dynamicComplementRealBandZeroPacket
                  S T
                  (dynamicMaximalComplementRealPart S T)
                  (dynamicMaximalComplementBandWidth S T) n) ∧
                dynamicComplementRealBandZeroPacket
                    S T
                    (dynamicMaximalComplementRealPart S T)
                    (dynamicMaximalComplementBandWidth S T) n ⊆
                  nontrivialZerosFinset T ∧
                  S.card <
                    (S ∪ dynamicComplementRealBandZeroPacket
                      S T
                      (dynamicMaximalComplementRealPart S T)
                      (dynamicMaximalComplementBandWidth S T) n).card ∧
                    ∀ rho ∈ dynamicComplementRealBandZeroPacket
                        S T
                        (dynamicMaximalComplementRealPart S T)
                        (dynamicMaximalComplementBandWidth S T) n,
                      rho.re = dynamicMaximalComplementRealPart S T := by
  classical
  rcases
      exists_dynamicMaximalOutsideForwardMovingGaussianSecondMoment_le_log_sq
      with ⟨C, hC, houtside⟩
  refine ⟨C, hC, ?_⟩
  intro S T a eta m L K hT ha heta hm hL hK hlarge
  have hm0 : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have houtsideBound :=
    houtside S T a K (m := m) (L := L) hT ha hm0
  have hlargeActual :
      2 *
          (2 * eta +
            2 *
              (1 - Real.exp
                (-dynamicMaximalComplementBandWidth S T * L)) ^ 2 *
              (∑ n ∈ K,
                dynamicComplementRealBandPacketCoefficientMass
                  S T
                  (dynamicMaximalComplementRealPart S T) a
                  (dynamicMaximalComplementBandWidth S T) n) ^ 2) +
          2 *
            dynamicComplementOutsideRealBandForwardMovingGaussianSecondMoment
              S T
              (dynamicMaximalComplementRealPart S T) a
              (dynamicMaximalComplementBandWidth S T) K m L <
        dynamicComplementForwardMovingGaussianSecondMoment
          S T (dynamicMaximalComplementRealPart S T) a K m L := by
    nlinarith
  rcases
      exists_absorbableDynamicComplementRealBandPacket_of_fullMovingGaussianL2_gt
        heta hm hL
        (dynamicMaximalComplementBandWidth_pos S T).le hK hlargeActual
      with
        ⟨n, hnK, hmass, hnonempty, hdisjoint, hsubset, hcard, hband⟩
  refine
    ⟨n, hnK, hmass, hnonempty, hdisjoint, hsubset, hcard, ?_⟩
  intro rho hrho
  have hrhoComplement :
      rho ∈ dynamicComplementZeroSet S T := by
    have hrhoFiltered := (Finset.mem_filter.mp hrho).1
    change
      rho ∈ zeroOrdinateUnitBucket n ∩
        (nontrivialZerosFinset T \ S) at hrhoFiltered
    exact (Finset.mem_inter.mp hrhoFiltered).2
  exact
    (dynamicComplementRealBand_iff_re_eq_dynamicMaximal
      hrhoComplement).mp (hband rho hrho)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
