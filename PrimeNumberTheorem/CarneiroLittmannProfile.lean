import PrimeNumberTheorem.MonotoneExtremalKernel
import PrimeNumberTheorem.SincSquareIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Sinc
import Mathlib.MeasureTheory.Integral.Asymptotics
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.Prod

open Asymptotics Complex Filter MeasureTheory Set

namespace PrimeNumberTheorem
namespace DirichletPolynomial

/-- The two-sided tail profile associated to a density which is nonnegative on
the positive half-line and nonpositive on the negative half-line.  The factor
`2` matches the normalization of the Carneiro--Littmann majorant error. -/
noncomputable def signedRadialTailProfile (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then
    2 * ∫ t in Ici x, q t
  else
    2 * ∫ t in Iic x, -q t

/-- The positive-half-line tail integral, extended by zero to the negative
half-line.  This auxiliary operator packages the Fubini argument used for the
two sides of `signedRadialTailProfile`. -/
noncomputable def positiveTailIntegral (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  if 0 ≤ x then ∫ t in Ici x, q t else 0

private noncomputable def positiveTailKernel (q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.1 ∧ p.1 ≤ p.2 then q p.2 else 0

/-- The two-sided Fubini kernel underlying `signedRadialTailProfile`.  For a
fixed density point `t`, its `x`-support is the oriented segment from `0` to
`t`. -/
private noncomputable def signedRadialTailKernel
    (q : ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  if 0 ≤ p.1 ∧ p.1 ≤ p.2 then q p.2
  else if p.2 ≤ p.1 ∧ p.1 < 0 then -q p.2
  else 0

private theorem signedRadialTailKernel_aestronglyMeasurable
    {q : ℝ → ℝ} (hq : AEStronglyMeasurable q) :
    AEStronglyMeasurable (signedRadialTailKernel q)
      (volume.prod volume) := by
  let splus : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  let sminus : Set (ℝ × ℝ) := {p | p.2 ≤ p.1 ∧ p.1 < 0}
  have hsplus : MeasurableSet splus :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have hsminus : MeasurableSet sminus :=
    (measurableSet_le measurable_snd measurable_fst).inter
      (measurableSet_lt measurable_fst measurable_const)
  have heq : signedRadialTailKernel q =
      splus.indicator (fun p => q p.2) +
        sminus.indicator (fun p => -q p.2) := by
    funext p
    by_cases hp : 0 ≤ p.1 ∧ p.1 ≤ p.2
    · have hm : ¬(p.2 ≤ p.1 ∧ p.1 < 0) := by
        intro h
        linarith
      simp [signedRadialTailKernel, splus, sminus, Set.indicator, hp, hm]
    · by_cases hm : p.2 ≤ p.1 ∧ p.1 < 0 <;>
        simp [signedRadialTailKernel, splus, sminus, Set.indicator, hp, hm]
  rw [heq]
  exact (hq.comp_snd.indicator hsplus).add
    (hq.comp_snd.neg.indicator hsminus)

private theorem integrable_signedRadialTailKernel
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (signedRadialTailKernel q) (volume.prod volume) := by
  have hmeas :=
    signedRadialTailKernel_aestronglyMeasurable hq.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards with t
    by_cases ht : 0 ≤ t
    · have heq : (fun x : ℝ => signedRadialTailKernel q (x, t)) =
          (Icc 0 t).indicator (fun _ => q t) := by
        funext x
        simp only [signedRadialTailKernel]
        by_cases hx : 0 ≤ x ∧ x ≤ t
        · simp [hx, Set.indicator]
        · have hminus : ¬(t ≤ x ∧ x < 0) := by
            intro h
            linarith
          simp [hx, hminus, Set.indicator]
      rw [heq]
      exact (integrableOn_const (μ := volume) (s := Icc 0 t)
        isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
    · have htneg : t < 0 := lt_of_not_ge ht
      have heq : (fun x : ℝ => signedRadialTailKernel q (x, t)) =
          (Ico t 0).indicator (fun _ => -q t) := by
        funext x
        simp only [signedRadialTailKernel]
        by_cases hx : t ≤ x ∧ x < 0
        · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
            intro h
            linarith
          simp [hplus, hx, Set.indicator]
        · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
            intro h
            linarith
          simp [hplus, hx, Set.indicator]
      rw [heq]
      exact (integrableOn_const (μ := volume) (s := Ico t 0)
        measure_Ico_lt_top.ne).integrable_indicator measurableSet_Ico
  · convert hmoment.norm using 1
    funext t
    by_cases ht : 0 ≤ t
    · have heq : (fun x : ℝ => ‖signedRadialTailKernel q (x, t)‖) =
          (Icc 0 t).indicator (fun _ => ‖q t‖) := by
        funext x
        simp only [signedRadialTailKernel]
        by_cases hx : 0 ≤ x ∧ x ≤ t
        · simp [hx, Set.indicator]
        · have hminus : ¬(t ≤ x ∧ x < 0) := by
            intro h
            linarith
          simp [hx, hminus, Set.indicator]
      rw [heq, integral_indicator measurableSet_Icc]
      simp [ht, norm_mul, abs_of_nonneg ht]
    · have htneg : t < 0 := lt_of_not_ge ht
      have heq : (fun x : ℝ => ‖signedRadialTailKernel q (x, t)‖) =
          (Ico t 0).indicator (fun _ => ‖q t‖) := by
        funext x
        simp only [signedRadialTailKernel]
        by_cases hx : t ≤ x ∧ x < 0
        · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
            intro h
            linarith
          simp [hplus, hx, Set.indicator]
        · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
            intro h
            linarith
          simp [hplus, hx, Set.indicator]
      rw [heq, integral_indicator measurableSet_Ico]
      simp [htneg.le, norm_mul, abs_of_nonpos htneg.le]

private theorem signedRadialTailProfile_eq_kernelIntegral
    (q : ℝ → ℝ) (x : ℝ) :
    signedRadialTailProfile q x =
      2 * ∫ t, signedRadialTailKernel q (x, t) := by
  rw [signedRadialTailProfile]
  by_cases hx : 0 ≤ x
  · rw [if_pos hx]
    congr 1
    rw [← integral_indicator measurableSet_Ici]
    apply integral_congr_ae
    filter_upwards with t
    have hminus : ¬(t ≤ x ∧ x < 0) := by
      intro h
      exact (not_lt_of_ge hx) h.2
    simp [signedRadialTailKernel, Set.indicator, hminus, hx]
  · have hxneg : x < 0 := lt_of_not_ge hx
    rw [if_neg hx]
    congr 1
    rw [← integral_indicator measurableSet_Iic]
    apply integral_congr_ae
    filter_upwards with t
    have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
      intro h
      exact hx h.1
    simp [signedRadialTailKernel, Set.indicator, hplus, hxneg]

private theorem integrable_signedRadialTailKernel_mul_exp
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) (xi : ℝ) :
    Integrable (fun p : ℝ × ℝ =>
      ((signedRadialTailKernel q p : ℝ) : ℂ) *
        Complex.exp (Complex.I * (xi * p.1))) (volume.prod volume) := by
  apply (integrable_signedRadialTailKernel hq hmoment).ofReal.mul_bdd (c := 1)
  · fun_prop
  · filter_upwards with p
    simp [Complex.norm_exp]

private theorem integral_signedRadialTailKernel_mul_exp
    (q : ℝ → ℝ) {xi t : ℝ} (hxi : xi ≠ 0) :
    (∫ x : ℝ, ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
      Complex.exp (Complex.I * (xi * x))) =
        (q t : ℂ) *
          (Complex.exp ((Complex.I * (xi : ℂ)) * t) - 1) /
            (Complex.I * (xi : ℂ)) := by
  have hc : Complex.I * (xi : ℂ) ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr hxi)
  have hphase (x : ℝ) :
      Complex.I * (xi * x) = (Complex.I * (xi : ℂ)) * x := by
    ring
  by_cases ht : 0 ≤ t
  · have heq : (fun x : ℝ =>
        ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (xi * x))) =
        (Icc 0 t).indicator (fun x =>
          (q t : ℂ) * Complex.exp (Complex.I * (xi * x))) := by
      funext x
      by_cases hx : 0 ≤ x ∧ x ≤ t
      · simp [signedRadialTailKernel, Set.indicator, hx]
      · have hminus : ¬(t ≤ x ∧ x < 0) := by
          intro h
          linarith
        simp [signedRadialTailKernel, Set.indicator, hx, hminus]
    rw [heq, integral_indicator measurableSet_Icc,
      integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le ht]
    simp_rw [hphase]
    calc
      (∫ x in 0..t,
          (q t : ℂ) * Complex.exp ((Complex.I * (xi : ℂ)) * x)) =
          (q t : ℂ) *
            ∫ x in 0..t, Complex.exp ((Complex.I * (xi : ℂ)) * x) := by
        exact intervalIntegral.integral_const_mul (q t : ℂ)
          (fun x : ℝ => Complex.exp ((Complex.I * (xi : ℂ)) * x))
      _ = (q t : ℂ) *
          (Complex.exp ((Complex.I * (xi : ℂ)) * t) - 1) /
            (Complex.I * (xi : ℂ)) := by
        rw [integral_exp_mul_complex hc]
        push_cast
        simp
        ring

  · have htneg : t < 0 := lt_of_not_ge ht
    have heq : (fun x : ℝ =>
        ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (xi * x))) =
        (Ico t 0).indicator (fun x =>
          (-(q t) : ℂ) * Complex.exp (Complex.I * (xi * x))) := by
      funext x
      by_cases hx : t ≤ x ∧ x < 0
      · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
          intro h
          linarith
        simp [signedRadialTailKernel, Set.indicator, hplus, hx]
      · have hplus : ¬(0 ≤ x ∧ x ≤ t) := by
          intro h
          linarith
        simp [signedRadialTailKernel, Set.indicator, hplus, hx]
    rw [heq, integral_indicator measurableSet_Ico,
      integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le htneg.le]
    simp_rw [hphase]
    calc
      (∫ x in t..0,
          (-(q t) : ℂ) * Complex.exp ((Complex.I * (xi : ℂ)) * x)) =
          (-(q t) : ℂ) *
            ∫ x in t..0, Complex.exp ((Complex.I * (xi : ℂ)) * x) := by
        exact intervalIntegral.integral_const_mul (-(q t) : ℂ)
          (fun x : ℝ => Complex.exp ((Complex.I * (xi : ℂ)) * x))
      _ = (q t : ℂ) *
          (Complex.exp ((Complex.I * (xi : ℂ)) * t) - 1) /
            (Complex.I * (xi : ℂ)) := by
        rw [integral_exp_mul_complex hc]
        push_cast
        simp
        ring

/-- Fourier transform of a two-sided radial tail profile.  This Fubini
identity isolates the two concrete facts needed later: the total mass and the
high-frequency transform of the density. -/
theorem fourierKernel_signedRadialTailProfile_mul
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x))
    {xi : ℝ} (hxi : xi ≠ 0) :
    (Complex.I * (xi : ℂ)) * fourierKernel (signedRadialTailProfile q) xi =
      2 * (fourierKernel q xi - ((∫ x, q x : ℝ) : ℂ)) := by
  let c : ℂ := Complex.I * (xi : ℂ)
  have hc : c ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero (ofReal_ne_zero.mpr hxi)
  have hkernel := integrable_signedRadialTailKernel_mul_exp hq hmoment xi
  have hqComplex : Integrable (fun x : ℝ => (q x : ℂ)) := hq.ofReal
  have hqExp : Integrable (fun x : ℝ =>
      (q x : ℂ) * Complex.exp (Complex.I * (xi * x))) := by
    apply hqComplex.mul_bdd (c := 1)
    · fun_prop
    · filter_upwards with x
      simp [Complex.norm_exp]
  have houter (x : ℝ) :
      (signedRadialTailProfile q x : ℂ) *
          Complex.exp (Complex.I * (xi * x)) =
        2 * ∫ t : ℝ, ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
          Complex.exp (Complex.I * (xi * x)) := by
    have hint := MeasureTheory.integral_mul_const (μ := volume)
      (Complex.exp (Complex.I * (xi * x)))
      (fun t : ℝ => ((signedRadialTailKernel q (x, t) : ℝ) : ℂ))
    have hcast :
        (∫ t : ℝ, ((signedRadialTailKernel q (x, t) : ℝ) : ℂ)) =
          ((∫ t : ℝ, signedRadialTailKernel q (x, t) : ℝ) : ℂ) :=
      integral_ofReal
    calc
      (signedRadialTailProfile q x : ℂ) *
          Complex.exp (Complex.I * (xi * x)) =
          2 * (((∫ t : ℝ, signedRadialTailKernel q (x, t) : ℝ) : ℂ)) *
            Complex.exp (Complex.I * (xi * x)) := by
        rw [signedRadialTailProfile_eq_kernelIntegral]
        push_cast
        ring
      _ = 2 * (∫ t : ℝ,
            ((signedRadialTailKernel q (x, t) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (xi * x)) := by
        exact congrArg (fun z : ℂ =>
          2 * z * Complex.exp (Complex.I * (xi * x))) hcast.symm
      _ = 2 * ((∫ t : ℝ,
            ((signedRadialTailKernel q (x, t) : ℝ) : ℂ)) *
          Complex.exp (Complex.I * (xi * x))) := by ring
      _ = 2 * ∫ t : ℝ,
          ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
            Complex.exp (Complex.I * (xi * x)) := by
        exact congrArg (fun z : ℂ => 2 * z) hint.symm
  have hinner (t : ℝ) :
      (∫ x : ℝ, ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
        Complex.exp (Complex.I * (xi * x))) =
        c⁻¹ * ((q t : ℂ) * Complex.exp (Complex.I * (xi * t)) -
          (q t : ℂ)) := by
    rw [integral_signedRadialTailKernel_mul_exp q hxi]
    dsimp [c]
    field_simp
  have hconst :
      (∫ t : ℝ, c⁻¹ *
        ((q t : ℂ) * Complex.exp (Complex.I * (xi * t)) - (q t : ℂ))) =
        c⁻¹ * ∫ t : ℝ,
          ((q t : ℂ) * Complex.exp (Complex.I * (xi * t)) - (q t : ℂ)) :=
    MeasureTheory.integral_const_mul c⁻¹
      (fun t : ℝ =>
        (q t : ℂ) * Complex.exp (Complex.I * (xi * t)) - (q t : ℂ))
  have hqIntegral :
      (∫ t : ℝ, (q t : ℂ)) = ((∫ t : ℝ, q t : ℝ) : ℂ) :=
    integral_ofReal
  have hfourier :
      fourierKernel (signedRadialTailProfile q) xi =
        2 * c⁻¹ *
          (fourierKernel q xi - ((∫ x, q x : ℝ) : ℂ)) := by
    unfold fourierKernel
    calc
      (∫ x : ℝ, (signedRadialTailProfile q x : ℂ) *
          Complex.exp (Complex.I * (xi * x))) =
          ∫ x : ℝ, 2 *
            (∫ t : ℝ, ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
              Complex.exp (Complex.I * (xi * x))) := by
        apply integral_congr_ae
        filter_upwards with x
        exact houter x
      _ = 2 * ∫ x : ℝ, ∫ t : ℝ,
            ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
              Complex.exp (Complex.I * (xi * x)) := by
        exact MeasureTheory.integral_const_mul 2
          (fun x : ℝ => ∫ t : ℝ,
            ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
              Complex.exp (Complex.I * (xi * x)))
      _ = 2 * ∫ t : ℝ, ∫ x : ℝ,
            ((signedRadialTailKernel q (x, t) : ℝ) : ℂ) *
              Complex.exp (Complex.I * (xi * x)) := by
        rw [integral_integral_swap hkernel]
      _ = 2 * ∫ t : ℝ,
            c⁻¹ * ((q t : ℂ) * Complex.exp (Complex.I * (xi * t)) -
              (q t : ℂ)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards with t
        exact hinner t
      _ = 2 * (c⁻¹ * ∫ t : ℝ,
            ((q t : ℂ) * Complex.exp (Complex.I * (xi * t)) -
              (q t : ℂ))) := by
        rw [hconst]
      _ = 2 * c⁻¹ *
          (fourierKernel q xi - ((∫ x, q x : ℝ) : ℂ)) := by
        rw [integral_sub hqExp hqComplex, hqIntegral]
        unfold fourierKernel
        ring
  rw [hfourier]
  field_simp
  ring

private theorem positiveTailKernel_aestronglyMeasurable
    {q : ℝ → ℝ} (hq : AEStronglyMeasurable q) :
    AEStronglyMeasurable (positiveTailKernel q) (volume.prod volume) := by
  let s : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2}
  have hs : MeasurableSet s :=
    (measurableSet_le measurable_const measurable_fst).inter
      (measurableSet_le measurable_fst measurable_snd)
  have heq : positiveTailKernel q = s.indicator (fun p => q p.2) := by
    funext p
    simp [positiveTailKernel, s, Set.indicator]
  rw [heq]
  exact hq.comp_snd.indicator hs

private theorem integrable_positiveTailKernel
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (positiveTailKernel q) (volume.prod volume) := by
  have hmeas := positiveTailKernel_aestronglyMeasurable hq.aestronglyMeasurable
  apply (integrable_prod_iff' hmeas).2
  constructor
  · filter_upwards with t
    have heq : (fun x : ℝ => positiveTailKernel q (x, t)) =
        (Icc 0 t).indicator (fun _ => q t) := by
      funext x
      simp [positiveTailKernel, Set.indicator]
    rw [heq]
    exact (integrableOn_const (μ := volume) (s := Icc 0 t)
      isCompact_Icc.measure_lt_top.ne).integrable_indicator measurableSet_Icc
  · have hnorm : Integrable (fun t : ℝ => ‖t * q t‖) := hmoment.norm
    have hindicator := hnorm.indicator (s := Ici 0) measurableSet_Ici
    convert hindicator using 1
    funext t
    by_cases ht : 0 ≤ t
    · have heq : (fun x : ℝ => ‖positiveTailKernel q (x, t)‖) =
          (Icc 0 t).indicator (fun _ => ‖q t‖) := by
        funext x
        by_cases hx : 0 ≤ x ∧ x ≤ t <;>
          simp [positiveTailKernel, Set.indicator, hx]
      rw [heq, integral_indicator measurableSet_Icc]
      simp [ht, norm_mul, abs_of_nonneg ht]
    · have heq : (fun x : ℝ => ‖positiveTailKernel q (x, t)‖) = 0 := by
        funext x
        simp only [positiveTailKernel]
        split_ifs with hx
        · exfalso
          exact ht (hx.1.trans hx.2)
        · simp
      rw [heq]
      simp [ht]

/-- A density with an integrable first moment has an integrable tail integral
on the positive half-line. -/
theorem integrable_positiveTailIntegral
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (positiveTailIntegral q) := by
  have hkernel := integrable_positiveTailKernel hq hmoment
  have hinner := hkernel.integral_prod_left
  convert hinner using 1
  funext x
  by_cases hx : 0 ≤ x
  · have heq : (fun t : ℝ => positiveTailKernel q (x, t)) =
        (Ici x).indicator q := by
      funext t
      simp [positiveTailKernel, Set.indicator, hx]
    rw [positiveTailIntegral, if_pos hx, heq, integral_indicator measurableSet_Ici]
  · have heq : (fun t : ℝ => positiveTailKernel q (x, t)) = 0 := by
      funext t
      simp [positiveTailKernel, hx]
    rw [positiveTailIntegral, if_neg hx, heq]
    simp

/-- Fubini's identity for a positive-half-line tail integral: integrating the
tail once more multiplies the density by the length `t` of `[0, t]`. -/
theorem integral_positiveTailIntegral
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    ∫ x, positiveTailIntegral q x =
      ∫ x in Ici 0, x * q x := by
  have hkernel := integrable_positiveTailKernel hq hmoment
  calc
    ∫ x, positiveTailIntegral q x =
        ∫ x, ∫ t, positiveTailKernel q (x, t) := by
      apply integral_congr_ae
      filter_upwards with x
      by_cases hx : 0 ≤ x
      · have heq : (fun t : ℝ => positiveTailKernel q (x, t)) =
            (Ici x).indicator q := by
          funext t
          simp [positiveTailKernel, Set.indicator, hx]
        rw [positiveTailIntegral, if_pos hx, heq,
          integral_indicator measurableSet_Ici]
      · have heq : (fun t : ℝ => positiveTailKernel q (x, t)) = 0 := by
          funext t
          simp [positiveTailKernel, hx]
        rw [positiveTailIntegral, if_neg hx, heq]
        simp
    _ = ∫ p, positiveTailKernel q p :=
      (integral_prod (positiveTailKernel q) hkernel).symm
    _ = ∫ t, ∫ x, positiveTailKernel q (x, t) :=
      integral_prod_symm (positiveTailKernel q) hkernel
    _ = ∫ x in Ici 0, x * q x := by
      rw [← integral_indicator measurableSet_Ici]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : 0 ≤ t
      · have heq : (fun x : ℝ => positiveTailKernel q (x, t)) =
            (Icc 0 t).indicator (fun _ => q t) := by
          funext x
          simp [positiveTailKernel, Set.indicator]
        rw [heq, integral_indicator measurableSet_Icc]
        simp [ht]
      · have heq : (fun x : ℝ => positiveTailKernel q (x, t)) = 0 := by
          funext x
          simp only [positiveTailKernel]
          split_ifs with hx
          · exfalso
            exact ht (hx.1.trans hx.2)
          · simp
        rw [heq]
        simp [ht]

private noncomputable def reflectedSignedDensity (q : ℝ → ℝ) (x : ℝ) : ℝ :=
  -q (-x)

private theorem integrable_reflectedSignedDensity
    {q : ℝ → ℝ} (hq : Integrable q) :
    Integrable (reflectedSignedDensity q) := by
  have hcomp : Integrable (q ∘ fun x : ℝ => -x) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hq
  apply hcomp.neg.congr
  filter_upwards with x
  rfl

private theorem integrable_id_mul_reflectedSignedDensity
    {q : ℝ → ℝ} (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (fun x : ℝ => x * reflectedSignedDensity q x) := by
  have hcomp : Integrable ((fun x : ℝ => x * q x) ∘ fun x : ℝ => -x) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hmoment
  apply hcomp.congr
  filter_upwards with x
  simp [reflectedSignedDensity, Function.comp_apply]

private theorem positiveTailIntegral_reflectedSignedDensity_neg
    {q : ℝ → ℝ} {x : ℝ} (hx : x < 0) :
    positiveTailIntegral (reflectedSignedDensity q) (-x) =
      ∫ t in Iic x, -q t := by
  rw [positiveTailIntegral, if_pos (neg_nonneg.mpr hx.le)]
  simp only [reflectedSignedDensity]
  rw [integral_Ici_eq_integral_Ioi]
  simpa using integral_comp_neg_Ioi (-x) (fun t : ℝ => -q t)

/-- If both the density and its signed first moment are integrable, then the
two-sided signed radial tail profile is integrable. -/
theorem integrable_signedRadialTailProfile
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    Integrable (signedRadialTailProfile q) := by
  have hplus : Integrable (positiveTailIntegral q) :=
    integrable_positiveTailIntegral hq hmoment
  have hreflected : Integrable (reflectedSignedDensity q) :=
    integrable_reflectedSignedDensity hq
  have hreflectedMoment :
      Integrable (fun x : ℝ => x * reflectedSignedDensity q x) :=
    integrable_id_mul_reflectedSignedDensity hmoment
  have hminus : Integrable (positiveTailIntegral (reflectedSignedDensity q)) :=
    integrable_positiveTailIntegral hreflected hreflectedMoment
  have hminusComp : Integrable
      (positiveTailIntegral (reflectedSignedDensity q) ∘ fun x : ℝ => -x) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hminus
  have hpiece : Integrable ((Ici (0 : ℝ)).piecewise
      (fun x => 2 * positiveTailIntegral q x)
      (fun x => 2 * positiveTailIntegral (reflectedSignedDensity q) (-x))) :=
    Integrable.piecewise measurableSet_Ici (hplus.const_mul 2).integrableOn
      (by simpa [Function.comp_apply] using (hminusComp.const_mul 2).integrableOn)
  apply hpiece.congr
  filter_upwards with x
  by_cases hx : 0 ≤ x
  · simp [signedRadialTailProfile, positiveTailIntegral, Set.piecewise, hx]
  · have hxlt : x < 0 := lt_of_not_ge hx
    simp only [signedRadialTailProfile, Set.piecewise, mem_Ici, hx]
    rw [positiveTailIntegral_reflectedSignedDensity_neg hxlt]
    simp

/-- The total mass of a signed radial tail profile is twice the first moment
of its density.  No sign hypothesis is needed; absolute integrability of the
density and its first moment justifies both Fubini interchanges. -/
theorem integral_signedRadialTailProfile
    {q : ℝ → ℝ}
    (hq : Integrable q)
    (hmoment : Integrable (fun x : ℝ => x * q x)) :
    ∫ x, signedRadialTailProfile q x =
      2 * ∫ x, x * q x := by
  let r : ℝ → ℝ := reflectedSignedDensity q
  have hr : Integrable r := integrable_reflectedSignedDensity hq
  have hrMoment : Integrable (fun x : ℝ => x * r x) :=
    integrable_id_mul_reflectedSignedDensity hmoment
  have hplus : Integrable (positiveTailIntegral q) :=
    integrable_positiveTailIntegral hq hmoment
  have hminus : Integrable (positiveTailIntegral r) :=
    integrable_positiveTailIntegral hr hrMoment
  have hminusComp : Integrable
      (positiveTailIntegral r ∘ fun x : ℝ => -x) :=
    (Measure.measurePreserving_neg volume).integrable_comp_of_integrable hminus
  have hne : ∀ᵐ x : ℝ, x ≠ 0 := by
    rw [ae_iff]
    simp
  have hprofile : signedRadialTailProfile q =ᵐ[volume]
      fun x => 2 * positiveTailIntegral q x +
        2 * positiveTailIntegral r (-x) := by
    filter_upwards [hne] with x hx0
    by_cases hx : 0 ≤ x
    · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
      simp [signedRadialTailProfile, positiveTailIntegral, r, hx, hxpos]
    · have hxneg : x < 0 := lt_of_not_ge hx
      rw [signedRadialTailProfile, if_neg hx,
        positiveTailIntegral_reflectedSignedDensity_neg hxneg]
      simp [positiveTailIntegral, hx]
  have hreflectIntegral :
      ∫ x, positiveTailIntegral r (-x) =
        ∫ x, positiveTailIntegral r x := by
    simpa [Function.comp_apply] using
      (Measure.measurePreserving_neg volume).integral_comp
        measurableEmbedding_neg (positiveTailIntegral r)
  have hrMomentSet :
      ∫ x in Ici 0, x * r x =
        ∫ x in Iic 0, x * q x := by
    rw [integral_Ici_eq_integral_Ioi]
    simpa [r, reflectedSignedDensity] using
      integral_comp_neg_Ioi 0 (fun x : ℝ => x * q x)
  have hsplit :
      (∫ x in Ici 0, x * q x) + (∫ x in Iio 0, x * q x) =
        ∫ x, x * q x := by
    simpa using integral_add_compl measurableSet_Ici hmoment
  have hplusIntegral := integral_positiveTailIntegral hq hmoment
  have hminusIntegral := integral_positiveTailIntegral hr hrMoment
  calc
    ∫ x, signedRadialTailProfile q x =
        ∫ x, (2 * positiveTailIntegral q x +
          2 * positiveTailIntegral r (-x)) :=
      integral_congr_ae hprofile
    _ = 2 * (∫ x, positiveTailIntegral q x) +
        2 * (∫ x, positiveTailIntegral r (-x)) := by
      rw [integral_add (hplus.const_mul 2)
        (by simpa [Function.comp_apply] using hminusComp.const_mul 2)]
      simp only [integral_const_mul]
    _ = 2 * (∫ x in Ici 0, x * q x) +
        2 * (∫ x in Ici 0, x * r x) := by
      rw [hreflectIntegral, hplusIntegral, hminusIntegral]
    _ = 2 * ∫ x, x * q x := by
      rw [hrMomentSet, integral_Iic_eq_integral_Iio]
      linear_combination 2 * hsplit

theorem signedRadialTailProfile_nonnegative
    {q : ℝ → ℝ}
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) (x : ℝ) :
    0 ≤ signedRadialTailProfile q x := by
  rw [signedRadialTailProfile]
  split_ifs with hx
  · exact mul_nonneg (by norm_num) <|
      setIntegral_nonneg measurableSet_Ici fun t ht => hpos t (hx.trans ht)
  · have hx' : x ≤ 0 := le_of_not_ge hx
    exact mul_nonneg (by norm_num) <|
      setIntegral_nonneg measurableSet_Iic fun t ht =>
        neg_nonneg.mpr (hneg t (ht.trans hx'))

/-- On the nonnegative half-line, moving the lower endpoint to the right can
only decrease the positive tail integral. -/
theorem signedRadialTailProfile_antitoneOn_nonnegative
    {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x) :
    AntitoneOn (signedRadialTailProfile q) (Ioi 0) := by
  intro x hx y hy hxy
  change 0 < x at hx
  change 0 < y at hy
  simp only [signedRadialTailProfile, if_pos hx.le, if_pos hy.le]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hq.integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
    exact hpos t (hx.trans_le ht).le
  · exact (Ici_subset_Ici.mpr hxy).eventuallyLE

/-- On the nonpositive half-line, moving the upper endpoint to the right can
only increase the tail integral of the negated density. -/
theorem signedRadialTailProfile_monotoneOn_nonpositive
    {q : ℝ → ℝ} (hq : Integrable q)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0) :
    MonotoneOn (signedRadialTailProfile q) (Iio 0) := by
  intro x hx y hy hxy
  change x < 0 at hx
  change y < 0 at hy
  simp only [signedRadialTailProfile, if_neg (not_le_of_gt hx),
    if_neg (not_le_of_gt hy)]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply setIntegral_mono_set hq.neg.integrableOn
  · filter_upwards [ae_restrict_mem measurableSet_Iic] with t ht
    exact neg_nonneg.mpr (hneg t (ht.trans hy.le))
  · exact (Iic_subset_Iic.mpr hxy).eventuallyLE

/-- Positive dilation shrinks the profile pointwise when its scale increases.
This is the exact monotonicity field required by
`MonotoneExtremalKernelCertificate`. -/
theorem signedRadialTailProfile_dilation_antitone
    {q : ℝ → ℝ} (hq : Integrable q)
    (hpos : ∀ x, 0 ≤ x → 0 ≤ q x)
    (hneg : ∀ x, x ≤ 0 → q x ≤ 0)
    {deltaNew deltaOld : ℝ}
    (hNew : 0 < deltaNew) (horder : deltaNew ≤ deltaOld) (t : ℝ) :
    signedRadialTailProfile q (deltaOld * t) ≤
      signedRadialTailProfile q (deltaNew * t) := by
  have hOld : 0 < deltaOld := hNew.trans_le horder
  by_cases ht0 : t = 0
  · subst t
    simp
  by_cases ht : 0 < t
  · exact signedRadialTailProfile_antitoneOn_nonnegative hq hpos
      (mul_pos hNew ht) (mul_pos hOld ht)
      (mul_le_mul_of_nonneg_right horder ht.le)
  · have ht' : t < 0 := lt_of_le_of_ne (le_of_not_gt ht) ht0
    exact signedRadialTailProfile_monotoneOn_nonpositive hq hneg
      (mul_neg_of_pos_of_neg hOld ht')
      (mul_neg_of_pos_of_neg hNew ht')
      (mul_le_mul_of_nonpos_right horder ht'.le)

/-- The density appearing in the integral formula for the monotone
Carneiro--Littmann majorant of the sign function.  At the removable points
Lean's division convention assigns zero; changing finitely many values does
not affect the intended Lebesgue integrals. -/
noncomputable def carneiroLittmannDensity (x : ℝ) : ℝ :=
  Real.sin (Real.pi * x) ^ 2 /
    (Real.pi ^ 2 * x * (x + 1) ^ 2)

theorem carneiroLittmannDensity_nonnegative
    {x : ℝ} (hx : 0 ≤ x) :
    0 ≤ carneiroLittmannDensity x := by
  unfold carneiroLittmannDensity
  apply div_nonneg (sq_nonneg _)
  exact mul_nonneg (mul_nonneg (sq_nonneg _) hx) (sq_nonneg _)

theorem carneiroLittmannDensity_nonpositive
    {x : ℝ} (hx : x ≤ 0) :
    carneiroLittmannDensity x ≤ 0 := by
  unfold carneiroLittmannDensity
  apply div_nonpos_of_nonneg_of_nonpos (sq_nonneg _)
  exact mul_nonpos_of_nonpos_of_nonneg
    (mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hx) (sq_nonneg _)

/-- The density written using the removable singularity of `sin (pi * x)` at
zero.  This identity is also valid at `x = -1` because both sides use Lean's
division-by-zero convention there. -/
theorem carneiroLittmannDensity_eq_sinc_zero (x : ℝ) :
    carneiroLittmannDensity x =
      x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2 := by
  by_cases hx0 : x = 0
  · simp [hx0, carneiroLittmannDensity]
  by_cases hx1 : x + 1 = 0
  · have hx : x = -1 := by linarith
    subst x
    simp [carneiroLittmannDensity, Real.sin_neg]
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx0)]
  unfold carneiroLittmannDensity
  field_simp [Real.pi_ne_zero, hx0, hx1]

/-- The density written using the removable singularity at `x = -1`.  The
formula is valid away from that one point, including at `x = 0`. -/
theorem carneiroLittmannDensity_eq_sinc_neg_one
    {x : ℝ} (hx : x ≠ -1) :
    carneiroLittmannDensity x =
      Real.sinc (Real.pi * (x + 1)) ^ 2 / x := by
  by_cases hx0 : x = 0
  · simp [hx0, carneiroLittmannDensity]
  have hx1 : x + 1 ≠ 0 := by
    intro hx1
    apply hx
    linarith
  rw [Real.sinc_of_ne_zero (mul_ne_zero Real.pi_ne_zero hx1)]
  have hsin : Real.sin (Real.pi * (x + 1)) = -Real.sin (Real.pi * x) := by
    rw [mul_add, mul_one, Real.sin_add_pi]
  rw [hsin]
  unfold carneiroLittmannDensity
  field_simp [Real.pi_ne_zero, hx0, hx1]

/-- A continuous representative of `carneiroLittmannDensity`.  The left-hand
formula removes the singularity at `-1`; the right-hand formula removes the
singularity at `0`. -/
noncomputable def carneiroLittmannRegularizedDensity (x : ℝ) : ℝ :=
  if x ≤ -(1 / 2 : ℝ) then
    Real.sinc (Real.pi * (x + 1)) ^ 2 / x
  else
    x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2

theorem continuous_carneiroLittmannRegularizedDensity :
    Continuous carneiroLittmannRegularizedDensity := by
  have hleft : ContinuousOn
      (fun x : ℝ => Real.sinc (Real.pi * (x + 1)) ^ 2 / x)
      (Iic (-(1 / 2 : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      change x ≤ -(1 / 2 : ℝ) at hx
      linarith
  have hright : ContinuousOn
      (fun x : ℝ => x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2)
      (Ici (-(1 / 2 : ℝ))) := by
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro x hx
      change -(1 / 2 : ℝ) ≤ x at hx
      have : x + 1 ≠ 0 := by linarith
      exact pow_ne_zero 2 this
  change Continuous (fun x : ℝ =>
    if x ≤ -(1 / 2 : ℝ) then
      Real.sinc (Real.pi * (x + 1)) ^ 2 / x
    else
      x * Real.sinc (Real.pi * x) ^ 2 / (x + 1) ^ 2)
  apply continuous_if_le continuous_id continuous_const hleft hright
  intro x hx
  change x = -(1 / 2 : ℝ) at hx
  subst x
  rw [← carneiroLittmannDensity_eq_sinc_neg_one (by norm_num),
    ← carneiroLittmannDensity_eq_sinc_zero]

theorem carneiroLittmannDensity_ae_eq_regularized :
    carneiroLittmannDensity =ᵐ[volume]
      carneiroLittmannRegularizedDensity := by
  have hne : ∀ᵐ x ∂volume, x ≠ (-1 : ℝ) := by
    simp [ae_iff, measure_singleton]
  filter_upwards [hne] with x hx
  rw [carneiroLittmannRegularizedDensity]
  split_ifs
  · exact carneiroLittmannDensity_eq_sinc_neg_one hx
  · exact carneiroLittmannDensity_eq_sinc_zero x

theorem locallyIntegrable_carneiroLittmannDensity :
    LocallyIntegrable carneiroLittmannDensity :=
  continuous_carneiroLittmannRegularizedDensity.locallyIntegrable.congr
    carneiroLittmannDensity_ae_eq_regularized.symm

private theorem one_add_sq_le_density_denominator_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    1 + x ^ 2 ≤ Real.pi ^ 2 * x * (x + 1) ^ 2 := by
  have hx0 : 0 ≤ x := by linarith
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hcubic : 2 * x ^ 2 ≤ x * x ^ 2 :=
    mul_le_mul_of_nonneg_right hx (sq_nonneg x)
  have hpoly : 1 + x ^ 2 ≤ x * (x + 1) ^ 2 := by
    nlinarith [sq_nonneg x]
  apply hpoly.trans
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    mul_le_mul_of_nonneg_right hpi (mul_nonneg hx0 (sq_nonneg (x + 1)))

private theorem one_add_sq_le_four_mul_neg_density_denominator_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    1 + x ^ 2 ≤ 4 * (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
  let y := -x
  have hy : 2 ≤ y := by dsimp [y]; linarith
  have hy0 : 0 ≤ y := by linarith
  have hym1 : 0 ≤ y - 1 := by linarith
  have hhalf : y / 2 ≤ y - 1 := by linarith
  have hsq : (y / 2) ^ 2 ≤ (y - 1) ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hhalf)
      (add_nonneg (by positivity : 0 ≤ y - 1) (by positivity : 0 ≤ y / 2))]
  have hmul := mul_le_mul_of_nonneg_left hsq hy0
  have hcubic : 2 * y ^ 2 ≤ y * y ^ 2 :=
    mul_le_mul_of_nonneg_right hy (sq_nonneg y)
  have hone : 1 ≤ y ^ 2 := by nlinarith [sq_nonneg (y - 1)]
  have hpoly : 1 + y ^ 2 ≤ 4 * y * (y - 1) ^ 2 := by
    nlinarith
  have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
  have hden : 4 * y * (y - 1) ^ 2 ≤
      4 * (Real.pi ^ 2 * y * (y - 1) ^ 2) := by
    nlinarith [mul_nonneg hy0 (sq_nonneg (y - 1)),
      mul_le_mul_of_nonneg_right hpi (mul_nonneg hy0 (sq_nonneg (y - 1)))]
  dsimp [y] at hpoly hden ⊢
  nlinarith

theorem carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    ‖carneiroLittmannDensity x‖ ≤ ‖(1 + x ^ 2)⁻¹‖ := by
  have hx0 : 0 ≤ x := by linarith
  have hden : 0 < Real.pi ^ 2 * x * (x + 1) ^ 2 := by positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg (carneiroLittmannDensity_nonnegative hx0),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hone)]
  unfold carneiroLittmannDensity
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ (1 + x ^ 2)⁻¹ * (Real.pi ^ 2 * x * (x + 1) ^ 2) := by
      have h := one_add_sq_le_density_denominator_of_two_le hx
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hone).2 (by simpa using h)

theorem carneiroLittmannDensity_norm_le_four_inv_one_add_sq_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    ‖carneiroLittmannDensity x‖ ≤ 4 * ‖(1 + x ^ 2)⁻¹‖ := by
  have hx0 : x ≤ 0 := by linarith
  have hden : 0 < Real.pi ^ 2 * (-x) * (x + 1) ^ 2 := by
    have hxneg : 0 < -x := by linarith
    have hx1 : x + 1 ≠ 0 := by linarith
    positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [Real.norm_eq_abs, abs_of_nonpos (carneiroLittmannDensity_nonpositive hx0),
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hone)]
  have hdensity : -carneiroLittmannDensity x =
      Real.sin (Real.pi * x) ^ 2 /
        (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
    have hxne : x ≠ 0 := by linarith
    have hx1 : x + 1 ≠ 0 := by linarith
    unfold carneiroLittmannDensity
    field_simp [Real.pi_ne_zero, hxne, hx1]
  rw [hdensity]
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ 4 * (1 + x ^ 2)⁻¹ *
        (Real.pi ^ 2 * (-x) * (x + 1) ^ 2) := by
      have h := one_add_sq_le_four_mul_neg_density_denominator_of_le_neg_two hx
      have hdiv : 1 ≤
          (4 * (Real.pi ^ 2 * (-x) * (x + 1) ^ 2)) / (1 + x ^ 2) :=
        (le_div_iff₀ hone).2 (by simpa using h)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

theorem carneiroLittmannDensity_isBigO_atTop :
    carneiroLittmannDensity =O[atTop]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ici_mem_atTop (2 : ℝ)] with x hx
  simpa using carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le hx

theorem carneiroLittmannDensity_isBigO_atBot :
    carneiroLittmannDensity =O[atBot]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 4
  filter_upwards [Iic_mem_atBot (-2 : ℝ)] with x hx
  exact carneiroLittmannDensity_norm_le_four_inv_one_add_sq_of_le_neg_two hx

theorem integrable_carneiroLittmannDensity :
    Integrable carneiroLittmannDensity :=
  locallyIntegrable_carneiroLittmannDensity.integrable_of_isBigO_atBot_atTop
    carneiroLittmannDensity_isBigO_atBot
    (integrable_inv_one_add_sq.integrableAtFilter atBot)
    carneiroLittmannDensity_isBigO_atTop
    (integrable_inv_one_add_sq.integrableAtFilter atTop)

private theorem id_mul_carneiroLittmannDensity_eq
    {x : ℝ} (hx : x ≠ 0) :
    x * carneiroLittmannDensity x =
      Real.sin (Real.pi * x) ^ 2 / (Real.pi ^ 2 * (x + 1) ^ 2) := by
  unfold carneiroLittmannDensity
  field_simp [Real.pi_ne_zero, hx]

/-- Away from the removable point `-1`, the first-moment integrand is a
translated normalized sinc square. -/
theorem id_mul_carneiroLittmannDensity_eq_sinc_shift
    {x : ℝ} (hx : x ≠ -1) :
    x * carneiroLittmannDensity x =
      Real.sinc (Real.pi * (x + 1)) ^ 2 := by
  by_cases hx0 : x = 0
  · subst x
    simp [carneiroLittmannDensity, Real.sinc_of_ne_zero Real.pi_ne_zero]
  · rw [carneiroLittmannDensity_eq_sinc_neg_one hx]
    field_simp

/-- The first-moment integrand agrees almost everywhere with the translated
normalized sinc square; the sole exceptional point is irrelevant to its
Lebesgue integral. -/
theorem id_mul_carneiroLittmannDensity_ae_eq_sinc_shift :
    (fun x : ℝ => x * carneiroLittmannDensity x) =ᵐ[volume]
      (fun x : ℝ => Real.sinc (Real.pi * (x + 1)) ^ 2) := by
  have hne : ∀ᵐ x : ℝ, x ≠ -1 := by
    rw [ae_iff]
    simp
  filter_upwards [hne] with x hx
  exact id_mul_carneiroLittmannDensity_eq_sinc_shift hx

private theorem locallyIntegrable_id_mul_carneiroLittmannDensity :
    LocallyIntegrable (fun x : ℝ => x * carneiroLittmannDensity x) := by
  apply (continuous_id.mul continuous_carneiroLittmannRegularizedDensity).locallyIntegrable.congr
  filter_upwards [carneiroLittmannDensity_ae_eq_regularized.symm] with x hx
  simp only [Pi.mul_apply, id_eq, hx]

private theorem id_mul_carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le
    {x : ℝ} (hx : 2 ≤ x) :
    ‖x * carneiroLittmannDensity x‖ ≤ ‖(1 + x ^ 2)⁻¹‖ := by
  have hx0 : 0 ≤ x := by linarith
  have hxne : x ≠ 0 := by linarith
  have hden : 0 < Real.pi ^ 2 * (x + 1) ^ 2 := by positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [id_mul_carneiroLittmannDensity_eq hxne, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le), Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hone)]
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ (1 + x ^ 2)⁻¹ * (Real.pi ^ 2 * (x + 1) ^ 2) := by
      have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
      have hpoly : 1 + x ^ 2 ≤ (x + 1) ^ 2 := by nlinarith
      have h : 1 + x ^ 2 ≤ Real.pi ^ 2 * (x + 1) ^ 2 :=
        hpoly.trans <| by
          simpa using mul_le_mul_of_nonneg_right hpi (sq_nonneg (x + 1))
      rw [inv_mul_eq_div]
      exact (le_div_iff₀ hone).2 (by simpa using h)

private theorem id_mul_carneiroLittmannDensity_norm_le_eight_inv_one_add_sq_of_le_neg_two
    {x : ℝ} (hx : x ≤ -2) :
    ‖x * carneiroLittmannDensity x‖ ≤ 8 * ‖(1 + x ^ 2)⁻¹‖ := by
  have hxne : x ≠ 0 := by linarith
  have hx1 : x + 1 ≠ 0 := by linarith
  have hden : 0 < Real.pi ^ 2 * (x + 1) ^ 2 := by positivity
  have hone : 0 < 1 + x ^ 2 := by positivity
  rw [id_mul_carneiroLittmannDensity_eq hxne, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sq_nonneg _) hden.le), Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hone)]
  apply (div_le_iff₀ hden).2
  calc
    Real.sin (Real.pi * x) ^ 2 ≤ 1 := by
      nlinarith [Real.neg_one_le_sin (Real.pi * x),
        Real.sin_le_one (Real.pi * x)]
    _ ≤ 8 * (1 + x ^ 2)⁻¹ * (Real.pi ^ 2 * (x + 1) ^ 2) := by
      have hpi : 1 ≤ Real.pi ^ 2 := by nlinarith [Real.two_le_pi]
      have hpoly : 1 + x ^ 2 ≤ 8 * (x + 1) ^ 2 := by
        nlinarith [sq_nonneg (x + 2)]
      have hden' : 8 * (x + 1) ^ 2 ≤
          8 * (Real.pi ^ 2 * (x + 1) ^ 2) := by
        nlinarith [sq_nonneg (x + 1),
          mul_le_mul_of_nonneg_right hpi (sq_nonneg (x + 1))]
      have h := hpoly.trans hden'
      have hdiv : 1 ≤
          (8 * (Real.pi ^ 2 * (x + 1) ^ 2)) / (1 + x ^ 2) :=
        (le_div_iff₀ hone).2 (by simpa using h)
      simpa [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hdiv

private theorem id_mul_carneiroLittmannDensity_isBigO_atTop :
    (fun x : ℝ => x * carneiroLittmannDensity x) =O[atTop]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 1
  filter_upwards [Ici_mem_atTop (2 : ℝ)] with x hx
  simpa using id_mul_carneiroLittmannDensity_norm_le_inv_one_add_sq_of_two_le hx

private theorem id_mul_carneiroLittmannDensity_isBigO_atBot :
    (fun x : ℝ => x * carneiroLittmannDensity x) =O[atBot]
      (fun x : ℝ => (1 + x ^ 2)⁻¹) := by
  apply IsBigO.of_bound 8
  filter_upwards [Iic_mem_atBot (-2 : ℝ)] with x hx
  exact id_mul_carneiroLittmannDensity_norm_le_eight_inv_one_add_sq_of_le_neg_two hx

theorem integrable_id_mul_carneiroLittmannDensity :
    Integrable (fun x : ℝ => x * carneiroLittmannDensity x) :=
  locallyIntegrable_id_mul_carneiroLittmannDensity.integrable_of_isBigO_atBot_atTop
    id_mul_carneiroLittmannDensity_isBigO_atBot
    (integrable_inv_one_add_sq.integrableAtFilter atBot)
    id_mul_carneiroLittmannDensity_isBigO_atTop
    (integrable_inv_one_add_sq.integrableAtFilter atTop)

theorem integrable_carneiroLittmannSincShiftSq :
    Integrable (fun x : ℝ =>
      Real.sinc (Real.pi * (x + 1)) ^ 2) :=
  integrable_id_mul_carneiroLittmannDensity.congr
    id_mul_carneiroLittmannDensity_ae_eq_sinc_shift

/-- The direct two-sided tail-integral candidate for `M - sgn`, where `M` is
the monotone Carneiro--Littmann majorant.  At the origin it uses the right-tail
normalization; this possible one-point difference is immaterial to the
Lebesgue integral and Fourier identities. -/
noncomputable def carneiroLittmannTailProfile (x : ℝ) : ℝ :=
  signedRadialTailProfile carneiroLittmannDensity x

theorem carneiroLittmannTailProfile_nonnegative (x : ℝ) :
    0 ≤ carneiroLittmannTailProfile x := by
  exact signedRadialTailProfile_nonnegative
    (fun _ => carneiroLittmannDensity_nonnegative)
    (fun _ => carneiroLittmannDensity_nonpositive) x

theorem integrable_carneiroLittmannTailProfile :
    Integrable carneiroLittmannTailProfile :=
  integrable_signedRadialTailProfile integrable_carneiroLittmannDensity
    integrable_id_mul_carneiroLittmannDensity

/-- The concrete profile mass is reduced to the standard full-line integral
of a translated normalized sinc square. -/
theorem integral_carneiroLittmannTailProfile_eq_sinc_shift :
    ∫ x, carneiroLittmannTailProfile x =
      2 * (∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2) := by
  change ∫ x, signedRadialTailProfile carneiroLittmannDensity x = _
  rw [integral_signedRadialTailProfile integrable_carneiroLittmannDensity
    integrable_id_mul_carneiroLittmannDensity]
  congr 1
  exact integral_congr_ae id_mul_carneiroLittmannDensity_ae_eq_sinc_shift

/-- Translation invariance and the substitution `u = pi * x` reduce the
shifted normalized sinc-square integral to the unscaled standard integral. -/
theorem integral_carneiroLittmannSincShiftSq_eq :
    ∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2 =
      Real.pi⁻¹ * ∫ u, Real.sinc u ^ 2 := by
  calc
    ∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2 =
        ∫ x, Real.sinc (Real.pi * x) ^ 2 := by
      simpa using integral_add_right_eq_self
        (fun x : ℝ => Real.sinc (Real.pi * x) ^ 2) 1
    _ = Real.pi⁻¹ * ∫ u, Real.sinc u ^ 2 := by
      simpa [abs_of_pos (inv_pos.mpr Real.pi_pos), smul_eq_mul] using
        Measure.integral_comp_mul_left (fun u : ℝ => Real.sinc u ^ 2) Real.pi

theorem integral_carneiroLittmannTailProfile_eq_sinc_sq :
    ∫ x, carneiroLittmannTailProfile x =
      2 * (Real.pi⁻¹ * ∫ u, Real.sinc u ^ 2) := by
  rw [integral_carneiroLittmannTailProfile_eq_sinc_shift,
    integral_carneiroLittmannSincShiftSq_eq]

theorem integral_carneiroLittmannTailProfile_eq_two :
    ∫ x, carneiroLittmannTailProfile x = 2 := by
  rw [integral_carneiroLittmannTailProfile_eq_sinc_sq,
    SincSquareIntegral.integral_sinc_sq]
  field_simp [Real.pi_ne_zero]

/-- The reciprocal Fourier-tail identity is the sole remaining hypothesis for
the concrete extremal-kernel certificate.  Integrability, nonnegativity,
mass normalization, and dilation monotonicity are all discharged here. -/
theorem carneiroLittmannTailProfile_certificate
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel carneiroLittmannTailProfile xi =
        (-2 * Complex.I) / xi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile where
  integrable := integrable_carneiroLittmannTailProfile
  nonnegative := carneiroLittmannTailProfile_nonnegative
  fourier_zero := by
    rw [fourierKernel_zero, integral_carneiroLittmannTailProfile_eq_two]
    norm_num
  fourier_tail := htail
  dilation_antitone := by
    intro deltaNew deltaOld hNew horder t
    exact signedRadialTailProfile_dilation_antitone
      integrable_carneiroLittmannDensity
      (fun _ => carneiroLittmannDensity_nonnegative)
      (fun _ => carneiroLittmannDensity_nonpositive) hNew horder t

/-- A normalized full-line sinc-square integral supplies the remaining mass
field of the concrete certificate.  The reciprocal Fourier tail remains a
separate analytic obligation. -/
theorem carneiroLittmannTailProfile_certificate_of_sinc_shift_integral
    (_hmass : ∫ x, Real.sinc (Real.pi * (x + 1)) ^ 2 = 1)
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel carneiroLittmannTailProfile xi =
        (-2 * Complex.I) / xi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile := by
  exact carneiroLittmannTailProfile_certificate htail

/-- The standard identity `integral sinc^2 = pi` supplies the concrete mass
normalization; only the reciprocal Fourier tail then remains. -/
theorem carneiroLittmannTailProfile_certificate_of_integral_sinc_sq
    (_hmass : ∫ x, Real.sinc x ^ 2 = Real.pi)
    (htail : ∀ xi : ℝ, 2 * Real.pi ≤ |xi| →
      fourierKernel carneiroLittmannTailProfile xi =
        (-2 * Complex.I) / xi) :
    MonotoneExtremalKernelCertificate carneiroLittmannTailProfile := by
  exact carneiroLittmannTailProfile_certificate htail

end DirichletPolynomial
end PrimeNumberTheorem
