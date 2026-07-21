import HardyTheorem.HardyPhaseHilbert
import Mathlib.MeasureTheory.Integral.Prod

open Complex MeasureTheory Set

namespace HardyTheorem

/-- The three-variable off-diagonal Hardy correlation on a dyadic block.

The product ordering is `(v, w, t)`, matching the order in which the two
short-window shifts are integrated before the long height variable. -/
noncomputable def hardyPhaseCorrelationOffDiagonalShiftKernel
    (s : Finset ℕ) (coeff : ℕ → ℂ) (p : (ℝ × ℝ) × ℝ) : ℂ :=
  hardyPhaseCorrelationOffDiagonal s coeff p.1.1 p.1.2 p.2

private theorem continuousAt_hardyPhaseCorrelationOffDiagonalShiftKernel
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) {p : (ℝ × ℝ) × ℝ}
    (htv : 0 < p.2 + p.1.1) (htw : 0 < p.2 + p.1.2) :
    ContinuousAt (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff) p := by
  have hargV : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1) p :=
    (continuous_snd.add continuous_fst.fst).continuousAt
  have hargW : ContinuousAt (fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2) p :=
    (continuous_snd.add continuous_fst.snd).continuousAt
  unfold hardyPhaseCorrelationOffDiagonalShiftKernel
    hardyPhaseCorrelationOffDiagonal
  apply tendsto_finset_sum
  intro m hm
  apply tendsto_finset_sum
  intro n hn
  by_cases hmn : m = n
  · simp [hmn]
  · simp only [hmn, ↓reduceIte]
    have hmphase : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          OscillatoryIntegral.hardyPhase m (q.2 + q.1.1)) p :=
      by
        change ContinuousAt
          (OscillatoryIntegral.hardyPhase m ∘
            fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1) p
        exact ContinuousAt.comp_of_eq
          (f := fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.1)
          (OscillatoryIntegral.contDiffAt_hardyPhase_two
            (hpositive m hm) htv).continuousAt hargV rfl
    have hnphase : ContinuousAt
        (fun q : (ℝ × ℝ) × ℝ =>
          OscillatoryIntegral.hardyPhase n (q.2 + q.1.2)) p :=
      by
        change ContinuousAt
          (OscillatoryIntegral.hardyPhase n ∘
            fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2) p
        exact ContinuousAt.comp_of_eq
          (f := fun q : (ℝ × ℝ) × ℝ => q.2 + q.1.2)
          (OscillatoryIntegral.contDiffAt_hardyPhase_two
            (hpositive n hn) htw).continuousAt hargW rfl
    unfold OscillatoryIntegral.hardyPhaseCorrelation
    exact (continuousAt_const.mul continuousAt_const).mul <|
      (continuousAt_const.mul
        (Complex.continuous_ofReal.continuousAt.comp
          (hmphase.sub hnphase))).cexp

/-- The off-diagonal Hardy correlation kernel is Bochner integrable on the
compact shift-height box used by the dyadic second-moment argument. -/
theorem integrable_hardyPhaseCorrelationOffDiagonalShiftKernel
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0)
    {T delta : ℝ} (hT : 0 < T) (hroom : delta ≤ T) :
    Integrable (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff)
      (((volume.restrict (Set.Ioc 0 delta)).prod
          (volume.restrict (Set.Ioc 0 delta))).prod
        (volume.restrict (Set.Ioc T (2 * T - delta)))) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let box : Set ((ℝ × ℝ) × ℝ) :=
    (Set.Icc 0 delta ×ˢ Set.Icc 0 delta) ×ˢ
      Set.Icc T (2 * T - delta)
  have hcompact : IsCompact box :=
    (isCompact_Icc.prod isCompact_Icc).prod isCompact_Icc
  have hcontinuous : ContinuousOn
      (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff) box := by
    intro p hp
    exact (continuousAt_hardyPhaseCorrelationOffDiagonalShiftKernel
      s coeff hpositive
      (by linarith [hT, hp.2.1, hp.1.1.1])
      (by linarith [hT, hp.2.1, hp.1.2.1])).continuousWithinAt
  have hbox : IntegrableOn
      (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff) box
      ((volume.prod volume).prod volume) :=
    hcontinuous.integrableOn_compact hcompact
  have hsmall : IntegrableOn
      (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff)
      ((Set.Ioc 0 delta ×ˢ Set.Ioc 0 delta) ×ˢ
        Set.Ioc T (2 * T - delta))
      ((volume.prod volume).prod volume) :=
    hbox.mono_set <| Set.prod_mono
      (Set.prod_mono Ioc_subset_Icc_self Ioc_subset_Icc_self)
      Ioc_subset_Icc_self
  simpa only [Measure.prod_restrict, IntegrableOn] using hsmall

/-- Fubini for the shift-averaged off-diagonal Hardy correlation.

The hypothesis is the exact Bochner-integrability condition for the kernel
on `[0, delta]² × [T, 2T-delta]`.  It is deliberately exposed: later
callers may discharge it either from joint continuity on the compact box or
from a separate majorant. -/
theorem hardyPhaseCorrelationOffDiagonal_shift_fubini
    (s : Finset ℕ) (coeff : ℕ → ℂ)
    {T delta : ℝ} (hdelta : 0 ≤ delta) (hroom : delta ≤ T)
    (hFubini : Integrable
      (hardyPhaseCorrelationOffDiagonalShiftKernel s coeff)
      (((volume.restrict (Set.Ioc 0 delta)).prod
          (volume.restrict (Set.Ioc 0 delta))).prod
        (volume.restrict (Set.Ioc T (2 * T - delta))))) :
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t) =
      ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    hardyPhaseCorrelationOffDiagonalShiftKernel s coeff
  have hF : Integrable F ((ν.prod ν).prod μ) := by
    simpa only [ν, μ, F] using hFubini
  have hswap :
      (∫ p, ∫ t, F (p, t) ∂μ ∂ν.prod ν) =
        ∫ t, ∫ p, F (p, t) ∂ν.prod ν ∂μ :=
    integral_integral_swap hF
  calc
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t) =
        ∫ p, ∫ t, F (p, t) ∂μ ∂ν.prod ν := by
      rw [integral_prod _ hF.integral_prod_left]
      simp only [ν, μ, F, intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        hardyPhaseCorrelationOffDiagonalShiftKernel]
    _ = ∫ t, ∫ p, F (p, t) ∂ν.prod ν ∂μ := hswap
    _ = ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t := by
      rw [intervalIntegral.integral_of_le hlong]
      apply integral_congr_ae
      filter_upwards [hF.prod_left_ae] with t ht
      rw [integral_prod _ ht]
      simp only [ν, F, intervalIntegral.integral_of_le hdelta,
        hardyPhaseCorrelationOffDiagonalShiftKernel]

/-- The Fubini identity with its integrability hypothesis discharged from
the dyadic positivity and positive-height assumptions. -/
theorem hardyPhaseCorrelationOffDiagonal_shift_fubini_dyadic
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    (∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t) =
      ∫ t in T..2 * T - delta, ∫ v in 0..delta, ∫ w in 0..delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t := by
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn hzero
    subst n
    have := hlower 0 hn
    omega
  exact hardyPhaseCorrelationOffDiagonal_shift_fubini s coeff hdelta hroom
    (integrable_hardyPhaseCorrelationOffDiagonalShiftKernel
      s coeff hpositive hT hroom)

/-- Integrating the uniform fixed-shift dyadic Hilbert bound over the square
`[0, delta]²` costs exactly its area `delta²`.

The only analytic hypothesis not already supplied by
`norm_integral_hardyPhaseCorrelationOffDiagonal_dyadic_le` is the precise
three-variable Bochner-integrability condition needed by Fubini. -/
theorem norm_integral_integral_integral_hardyPhaseCorrelationOffDiagonal_dyadic_le
    {M : ℕ} (hM : 0 < M) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hlower : ∀ n ∈ s, M ≤ n) (hupper : ∀ n ∈ s, n ≤ 2 * M)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ ≤
      delta ^ 2 *
        ((2 + delta / 2) * ((5 * Real.pi + 3) * M *
          (2 * ∑ n ∈ s, Complex.normSq (coeff n)))) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    hardyPhaseCorrelationOffDiagonalShiftKernel s coeff
  let B : ℝ :=
    (2 + delta / 2) * ((5 * Real.pi + 3) * M *
      (2 * ∑ n ∈ s, Complex.normSq (coeff n)))
  have hpositive : ∀ n ∈ s, n ≠ 0 := by
    intro n hn hzero
    subst n
    have := hlower 0 hn
    omega
  have hFubini : Integrable F ((ν.prod ν).prod μ) := by
    simpa only [ν, μ, F] using
      (integrable_hardyPhaseCorrelationOffDiagonalShiftKernel
        s coeff hpositive hT hroom)
  have hF : Integrable F ((ν.prod ν).prod μ) := by
    simpa only [ν, μ, F] using hFubini
  have hK : Integrable (fun p : ℝ × ℝ => ∫ t, F (p, t) ∂μ)
      (ν.prod ν) := hF.integral_prod_left
  have hpoint : ∀ᵐ p ∂ν.prod ν,
      ‖∫ t, F (p, t) ∂μ‖ ≤ B := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hv : p.1 ∈ Set.Icc 0 delta := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hw : p.2 ∈ Set.Icc 0 delta := ⟨le_of_lt hp.2.1, hp.2.2⟩
    simpa only [μ, F, B, intervalIntegral.integral_of_le hlong,
      hardyPhaseCorrelationOffDiagonalShiftKernel] using
      norm_integral_hardyPhaseCorrelationOffDiagonal_dyadic_le
        hM s coeff hlower hupper hT hdelta hroom hv hw
  have hmeasure : (ν.prod ν).real Set.univ = delta ^ 2 := by
    dsimp only [ν]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hdelta]
    ring
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ =
        ‖∫ p, ∫ t, F (p, t) ∂μ ∂ν.prod ν‖ := by
      rw [integral_prod _ hK]
      simp only [ν, μ, F, intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        hardyPhaseCorrelationOffDiagonalShiftKernel]
    _ ≤ B * (ν.prod ν).real Set.univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ = delta ^ 2 * B := by rw [hmeasure]; ring
    _ = delta ^ 2 *
        ((2 + delta / 2) * ((5 * Real.pi + 3) * M *
          (2 * ∑ n ∈ s, Complex.normSq (coeff n)))) := rfl

/-- Shift-averaged full off-diagonal bound under a global positive-index
cutoff.  In particular, cross-block interactions are retained rather than
estimated after a triangle inequality. -/
theorem norm_integral_integral_integral_hardyPhaseCorrelationOffDiagonal_le_of_upper
    {N : ℕ} (hN : 0 < N) (s : Finset ℕ) (coeff : ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {T delta : ℝ} (hT : 0 < T) (hdelta : 0 ≤ delta)
    (hroom : delta ≤ T) :
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ ≤
      delta ^ 2 *
        ((2 + delta / 2) * ((5 * Real.pi + 4) * N *
          (2 * ∑ n ∈ s, Complex.normSq (coeff n)))) := by
  have hlong : T ≤ 2 * T - delta := by linarith
  let ν : Measure ℝ := volume.restrict (Set.Ioc 0 delta)
  let μ : Measure ℝ := volume.restrict (Set.Ioc T (2 * T - delta))
  let F : (ℝ × ℝ) × ℝ → ℂ :=
    hardyPhaseCorrelationOffDiagonalShiftKernel s coeff
  let B : ℝ :=
    (2 + delta / 2) * ((5 * Real.pi + 4) * N *
      (2 * ∑ n ∈ s, Complex.normSq (coeff n)))
  have hF : Integrable F ((ν.prod ν).prod μ) := by
    simpa only [ν, μ, F] using
      (integrable_hardyPhaseCorrelationOffDiagonalShiftKernel
        s coeff hpositive hT hroom)
  have hK : Integrable (fun p : ℝ × ℝ => ∫ t, F (p, t) ∂μ)
      (ν.prod ν) := hF.integral_prod_left
  have hpoint : ∀ᵐ p ∂ν.prod ν,
      ‖∫ t, F (p, t) ∂μ‖ ≤ B := by
    dsimp only [ν]
    rw [Measure.prod_restrict]
    filter_upwards [ae_restrict_mem
      (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hv : p.1 ∈ Set.Icc 0 delta := ⟨le_of_lt hp.1.1, hp.1.2⟩
    have hw : p.2 ∈ Set.Icc 0 delta := ⟨le_of_lt hp.2.1, hp.2.2⟩
    simpa only [μ, F, B, intervalIntegral.integral_of_le hlong,
      hardyPhaseCorrelationOffDiagonalShiftKernel] using
      norm_integral_hardyPhaseCorrelationOffDiagonal_le_of_upper
        hN s coeff hpositive hupper hT hdelta hroom hv hw
  have hmeasure : (ν.prod ν).real Set.univ = delta ^ 2 := by
    dsimp only [ν]
    rw [Measure.prod_restrict, measureReal_def,
      Measure.restrict_apply_univ, Measure.prod_prod,
      Real.volume_Ioc, sub_zero, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hdelta]
    ring
  calc
    ‖∫ v in 0..delta, ∫ w in 0..delta, ∫ t in T..2 * T - delta,
        hardyPhaseCorrelationOffDiagonal s coeff v w t‖ =
        ‖∫ p, ∫ t, F (p, t) ∂μ ∂ν.prod ν‖ := by
      rw [integral_prod _ hK]
      simp only [ν, μ, F, intervalIntegral.integral_of_le hdelta,
        intervalIntegral.integral_of_le hlong,
        hardyPhaseCorrelationOffDiagonalShiftKernel]
    _ ≤ B * (ν.prod ν).real Set.univ :=
      norm_integral_le_of_norm_le_const hpoint
    _ = delta ^ 2 * B := by rw [hmeasure]; ring
    _ = delta ^ 2 *
        ((2 + delta / 2) * ((5 * Real.pi + 4) * N *
          (2 * ∑ n ∈ s, Complex.normSq (coeff n)))) := rfl

end HardyTheorem
