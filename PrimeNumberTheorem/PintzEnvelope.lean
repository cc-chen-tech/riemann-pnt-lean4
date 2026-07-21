import HardyTheorem.HardyIntegralContradiction
import PrimeNumberTheorem.GlobalZeroCount
import ZeroFreeRegion.PhragmenLindelofZeta

open Complex Filter Set Topology

namespace PrimeNumberTheorem
namespace Pintz

/-- The logarithmic cost associated with one nontrivial zeta zero in Pintz's
global error envelope. -/
noncomputable def pintzZeroTerm (x : ℝ) (rho : ℂ) : ℝ :=
  (1 - rho.re) * Real.log x + Real.log rho.im

/-- The one-variable lower model supplied by a classical `c / log t`
zero-free region. -/
noncomputable def pintzClassicalMinorant (c x t : ℝ) : ℝ :=
  (c / Real.log t) * Real.log x + Real.log t

/-- Values of the Pintz cost over all nontrivial zeta zeros in the open upper
half-plane. -/
noncomputable def pintzZeroEnvelopeValues (x : ℝ) : Set ℝ :=
  {y | ∃ rho : ℂ,
    RiemannHypothesis.IsNontrivialZero rho ∧
      0 < rho.im ∧ y = pintzZeroTerm x rho}

/-- Positive-height nontrivial zeros below the classical zero-free-region
cutoff. -/
def pintzLowZeros : Set ℂ :=
  {rho | RiemannHypothesis.IsNontrivialZero rho ∧
    0 < rho.im ∧ rho.im < 2}

/-- Pintz costs contributed by the finite low-zero family. -/
noncomputable def pintzLowZeroValues (x : ℝ) : Set ℝ :=
  pintzZeroTerm x '' pintzLowZeros

/-- The lower floor contributed by the finite low-zero family. -/
noncomputable def pintzLowZeroFloor (x : ℝ) : ℝ :=
  sInf (pintzLowZeroValues x)

/-- Pintz's zero envelope, defined as the infimum of the costs contributed by
all nontrivial zeta zeros of positive ordinate. -/
noncomputable def pintzZeroEnvelope (x : ℝ) : ℝ :=
  sInf (pintzZeroEnvelopeValues x)

/-- Hardy's theorem makes the upper-half-plane zero family nonempty. -/
theorem pintzZeroEnvelopeValues_nonempty (x : ℝ) :
    (pintzZeroEnvelopeValues x).Nonempty := by
  rcases HardyTheorem.hardy_zeros_unbounded_target_proved 1 with
    ⟨t, ht, hzero⟩
  have htpos : 0 < t := zero_lt_one.trans_le ht
  let rho : ℂ := (1 / 2 : ℂ) + I * t
  have hzeta : riemannZeta rho = 0 := by
    have hrho : rho = (0.5 : ℂ) + I * t := by norm_num [rho]
    rw [hrho]
    exact hzero
  have hrho : RiemannHypothesis.IsNontrivialZero rho := by
    refine ⟨hzeta, ?_, ?_⟩
    · norm_num [rho]
    · norm_num [rho]
  refine ⟨pintzZeroTerm x rho, ?_⟩
  exact ⟨rho, hrho, by simpa [rho] using htpos, rfl⟩

/-- There are only finitely many positive-height nontrivial zeros below
height two. -/
theorem finite_pintzLowZeros : pintzLowZeros.Finite := by
  apply (finite_nontrivial_zeros_bounded_height 2).subset
  intro rho hrho
  exact ⟨hrho.1, by simpa [abs_of_pos hrho.2.1] using hrho.2.2.le⟩

/-- The corresponding low-zero cost set is finite for every `x`. -/
theorem finite_pintzLowZeroValues (x : ℝ) :
    (pintzLowZeroValues x).Finite := by
  exact finite_pintzLowZeros.image (pintzZeroTerm x)

/-- For `x >= 1`, the set defining the Pintz envelope is bounded below.
Low zeros form a finite set; above height two every summand is nonnegative. -/
theorem bddBelow_pintzZeroEnvelopeValues {x : ℝ} (hx : 1 ≤ x) :
    BddBelow (pintzZeroEnvelopeValues x) := by
  rcases (finite_pintzLowZeroValues x).bddBelow with ⟨a, ha⟩
  refine ⟨min a 0, ?_⟩
  intro y hy
  rcases hy with ⟨rho, hrho, him, rfl⟩
  by_cases hlow : rho.im < 2
  · exact (min_le_left a 0).trans
      (ha ⟨rho, ⟨hrho, him, hlow⟩, rfl⟩)
  · apply (min_le_right a 0).trans
    have hfactor : 0 ≤ 1 - rho.re := sub_nonneg.mpr hrho.2.2.le
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
    have hlogim : 0 ≤ Real.log rho.im :=
      Real.log_nonneg (by linarith)
    exact add_nonneg (mul_nonneg hfactor hlogx) hlogim

/-- The proved classical zero-free region bounds the Pintz cost of every zero
above height two by its standard one-variable optimization model. -/
theorem exists_classicalMinorant_le_zeroTerm :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x → ∀ {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho → 2 ≤ rho.im →
        pintzClassicalMinorant c x rho.im ≤ pintzZeroTerm x rho := by
  rcases ZeroFreeRegion.classical_zero_free_region_proved with
    ⟨c, hc, hregion⟩
  refine ⟨c, hc, ?_⟩
  intro x hx rho hrho him
  have him_nonneg : 0 ≤ rho.im := le_trans (by norm_num) him
  have habs : |rho.im| = rho.im := abs_of_nonneg him_nonneg
  have hnot : ¬ 1 - c / Real.log |rho.im| ≤ rho.re := by
    intro hre
    exact (hregion rho (by simpa [habs] using him) hre) hrho.1
  have hgap : c / Real.log rho.im ≤ 1 - rho.re := by
    rw [habs] at hnot
    linarith
  have hmul := mul_le_mul_of_nonneg_right hgap (Real.log_nonneg hx)
  simpa [pintzClassicalMinorant, pintzZeroTerm] using
    add_le_add_right hmul (Real.log rho.im)

/-- Optimizing the classical one-variable model by the elementary inequality
`a / u + u >= 2 * sqrt a`. -/
theorem two_mul_sqrt_le_classicalMinorant {c x t : ℝ}
    (hc : 0 < c) (hx : 1 ≤ x) (ht : 2 ≤ t) :
    2 * Real.sqrt (c * Real.log x) ≤ pintzClassicalMinorant c x t := by
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hct : 0 ≤ c * Real.log x := mul_nonneg hc.le hlogx
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hsquare : (Real.sqrt (c * Real.log x)) ^ 2 = c * Real.log x :=
    Real.sq_sqrt hct
  apply le_of_mul_le_mul_right ?_ hlogt
  rw [pintzClassicalMinorant]
  have hdenom : Real.log t ≠ 0 := ne_of_gt hlogt
  calc
    (2 * Real.sqrt (c * Real.log x)) * Real.log t ≤
        c * Real.log x + (Real.log t) ^ 2 := by
      nlinarith [sq_nonneg (Real.sqrt (c * Real.log x) - Real.log t)]
    _ = ((c / Real.log t) * Real.log x + Real.log t) * Real.log t := by
      field_simp

/-- Consequently, all nontrivial zeros above height two have Pintz cost at
least a fixed positive multiple of `sqrt (log x)`. -/
theorem exists_two_mul_sqrt_le_highZeroTerm :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x → ∀ {rho : ℂ},
      RiemannHypothesis.IsNontrivialZero rho → 2 ≤ rho.im →
        2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho := by
  rcases exists_classicalMinorant_le_zeroTerm with ⟨c, hc, hminorant⟩
  refine ⟨c, hc, ?_⟩
  intro x hx rho hrho him
  exact (two_mul_sqrt_le_classicalMinorant hc hx him).trans
    (hminorant hx hrho him)

/-- Exact low/high decomposition of the full envelope.  The high-zero side is
controlled by the classical zero-free region; the only remaining term is the
finite low-zero floor. -/
theorem exists_min_lowFloor_two_mul_sqrt_le_zeroEnvelope :
    ∃ c > 0, ∀ {x : ℝ}, 1 ≤ x →
      min (pintzLowZeroFloor x) (2 * Real.sqrt (c * Real.log x)) ≤
        pintzZeroEnvelope x := by
  rcases exists_two_mul_sqrt_le_highZeroTerm with ⟨c, hc, hhigh⟩
  refine ⟨c, hc, ?_⟩
  intro x hx
  apply le_csInf (pintzZeroEnvelopeValues_nonempty x)
  intro value hvalue
  rcases hvalue with ⟨rho, hrho, him, rfl⟩
  by_cases hhighHeight : 2 ≤ rho.im
  · exact (min_le_right _ _).trans (hhigh hx hrho hhighHeight)
  · apply (min_le_left _ _).trans
    apply csInf_le (finite_pintzLowZeroValues x).bddBelow
    exact ⟨rho, ⟨hrho, him, lt_of_not_ge hhighHeight⟩, rfl⟩

/-- Each fixed low zero eventually has larger linear-in-`log x` cost than the
square-root scale coming from the high-zero optimization. -/
theorem eventually_two_mul_sqrt_le_lowZeroTerm {c : ℝ} (hc : 0 < c)
    {rho : ℂ} (hrho : rho ∈ pintzLowZeros) :
    ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho := by
  let d : ℝ := 1 - rho.re
  have hd : 0 < d := sub_pos.mpr hrho.1.2.2
  let b : ℝ := Real.log rho.im
  let K : ℝ := max 1 ((2 * Real.sqrt c + |b|) / d)
  have hsqrtLogTop :
      Tendsto (fun x : ℝ => Real.sqrt (Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp Real.tendsto_log_atTop
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      tendsto_atTop.1 hsqrtLogTop K] with x hx hu
  let u : ℝ := Real.sqrt (Real.log x)
  have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx
  have hu0 : 0 ≤ u := Real.sqrt_nonneg _
  have hu1 : 1 ≤ u := (le_max_left _ _).trans hu
  have hquot : (2 * Real.sqrt c + |b|) / d ≤ u :=
    (le_max_right _ _).trans hu
  have hdu : 2 * Real.sqrt c + |b| ≤ d * u :=
    by simpa [mul_comm] using (div_le_iff₀ hd).mp hquot
  have hprod :
      (2 * Real.sqrt c + |b|) * u ≤ (d * u) * u :=
    mul_le_mul_of_nonneg_right hdu hu0
  have habsprod : |b| ≤ |b| * u :=
    le_mul_of_one_le_right (abs_nonneg b) hu1
  have habsadd : 0 ≤ |b| + b := by
    linarith [neg_le_abs b]
  have hsqrtmul :
      Real.sqrt (c * Real.log x) = Real.sqrt c * u := by
    simpa [u] using Real.sqrt_mul (show 0 ≤ c from hc.le) (Real.log x)
  have husq : u ^ 2 = Real.log x := by
    simpa [u] using Real.sq_sqrt hlogx
  have htarget : 2 * Real.sqrt c * u ≤ d * Real.log x + b := by
    rw [← husq]
    nlinarith
  simpa [pintzZeroTerm, d, b, hsqrtmul, mul_assoc] using htarget

/-- The finite low-zero family satisfies the preceding estimate uniformly for
all sufficiently large `x`. -/
theorem eventually_all_lowZeroTerms_above_sqrt {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℝ in atTop, ∀ rho ∈ pintzLowZeros,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroTerm x rho := by
  exact finite_pintzLowZeros.eventually_all.mpr fun rho hrho =>
    eventually_two_mul_sqrt_le_lowZeroTerm hc hrho

/-- Unconditional classical lower bound for the full Pintz zero envelope.
This combines the proved classical zero-free region with finiteness of the
bounded-height zero set. -/
theorem exists_eventually_two_mul_sqrt_le_zeroEnvelope :
    ∃ c > 0, ∀ᶠ x : ℝ in atTop,
      2 * Real.sqrt (c * Real.log x) ≤ pintzZeroEnvelope x := by
  rcases exists_two_mul_sqrt_le_highZeroTerm with ⟨c, hc, hhigh⟩
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (1 : ℝ),
      eventually_all_lowZeroTerms_above_sqrt hc] with x hx hlow
  apply le_csInf (pintzZeroEnvelopeValues_nonempty x)
  intro value hvalue
  rcases hvalue with ⟨rho, hrho, him, rfl⟩
  by_cases hhighHeight : 2 ≤ rho.im
  · exact hhigh hx hrho hhighHeight
  · exact hlow rho ⟨hrho, him, lt_of_not_ge hhighHeight⟩

/-- The Pintz zero envelope tends to infinity. -/
theorem tendsto_pintzZeroEnvelope_atTop :
    Tendsto pintzZeroEnvelope atTop atTop := by
  rcases exists_eventually_two_mul_sqrt_le_zeroEnvelope with
    ⟨c, hc, henvelope⟩
  have hinside :
      Tendsto (fun x : ℝ => c * Real.log x) atTop atTop :=
    Real.tendsto_log_atTop.const_mul_atTop hc
  have hsqrt :
      Tendsto (fun x : ℝ => Real.sqrt (c * Real.log x)) atTop atTop :=
    Real.tendsto_sqrt_atTop.comp hinside
  have hscale :
      Tendsto (fun x : ℝ => 2 * Real.sqrt (c * Real.log x)) atTop atTop :=
    hsqrt.const_mul_atTop (by norm_num)
  exact tendsto_atTop_mono' atTop henvelope hscale

/-- The envelope is no larger than the contribution of any chosen positive
ordinate nontrivial zero. -/
theorem pintzZeroEnvelope_le_zeroTerm {x : ℝ} (hx : 1 ≤ x) {rho : ℂ}
    (hrho : RiemannHypothesis.IsNontrivialZero rho)
    (him : 0 < rho.im) :
    pintzZeroEnvelope x ≤ pintzZeroTerm x rho := by
  exact csInf_le (bddBelow_pintzZeroEnvelopeValues hx)
    ⟨rho, hrho, him, rfl⟩

/-- The Pintz zero envelope is monotone on its natural range `x >= 1`. -/
theorem monotoneOn_pintzZeroEnvelope :
    MonotoneOn pintzZeroEnvelope (Set.Ici 1) := by
  intro x hx y hy hxy
  apply le_csInf (pintzZeroEnvelopeValues_nonempty y)
  intro value hvalue
  rcases hvalue with ⟨rho, hrho, him, rfl⟩
  calc
    pintzZeroEnvelope x ≤ pintzZeroTerm x rho :=
      pintzZeroEnvelope_le_zeroTerm hx hrho him
    _ ≤ pintzZeroTerm y rho := by
      have hmul := mul_le_mul_of_nonneg_left
        (Real.log_le_log (lt_of_lt_of_le zero_lt_one hx) hxy)
        (sub_nonneg.mpr hrho.2.2.le)
      simpa [pintzZeroTerm] using
        add_le_add_right hmul (Real.log rho.im)

end Pintz
end PrimeNumberTheorem
