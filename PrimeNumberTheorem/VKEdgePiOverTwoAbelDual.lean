import PrimeNumberTheorem.VKEdgePiOverTwoAbelIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

open Filter MeasureTheory Set Topology

open scoped Interval

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-- Abel averaging on the positive half-line. -/
def realAbelMean (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  a * ∫ y : ℝ in Set.Ioi 0, Real.exp (-a * y) * f y

private lemma tendsto_exp_neg_mul_atTop_zero {a : ℝ} (ha : 0 < a) :
    Tendsto (fun y : ℝ => Real.exp (-a * y)) atTop (𝓝 0) := by
  have hlinear : Tendsto (fun y : ℝ => a * y) atTop atTop :=
    by simpa [mul_comm] using tendsto_id.atTop_mul_const ha
  simpa only [neg_mul] using
    Real.tendsto_exp_neg_atTop_nhds_zero.comp hlinear

private lemma integrableOn_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    IntegrableOn (fun y : ℝ => Real.exp (-a * y)) (Set.Ioi 0) := by
  simpa only [neg_mul] using
    integrableOn_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0

private lemma integral_exp_neg_mul_Ioi {a : ℝ} (ha : 0 < a) :
    (∫ y : ℝ in Set.Ioi 0, Real.exp (-a * y)) = 1 / a := by
  rw [show (fun y : ℝ => Real.exp (-a * y)) =
      fun y : ℝ => Real.exp ((-a) * y) by
        funext y
        ring_nf]
  rw [integral_exp_mul_Ioi (a := -a) (neg_neg_of_pos ha) 0]
  simp

/-- Abel averages of a continuous periodic real function converge to its
ordinary average over one positive period. -/
theorem tendsto_realAbelMean_of_continuous_periodic
    {f : ℝ → ℝ} {T : ℝ}
    (hT : 0 < T) (hf : Function.Periodic f T)
    (hcont : Continuous f) :
    Tendsto (realAbelMean f) (𝓝[>] 0)
      (𝓝 ((1 / T) * ∫ y in (0 : ℝ)..T, f y)) := by
  let m : ℝ := (1 / T) * ∫ y in (0 : ℝ)..T, f y
  let q : ℝ → ℝ := fun y => f y - m
  let P : ℝ → ℝ := fun x => ∫ y in (0 : ℝ)..x, q y
  have hqcont : Continuous q := hcont.sub continuous_const
  have hmper : Function.Periodic (fun _ : ℝ => m) T := by
    intro x
    rfl
  have hqper : Function.Periodic q T := hf.sub hmper
  have hqint : ∀ a b : ℝ, IntervalIntegrable q volume a b :=
    fun a b => hqcont.intervalIntegrable a b
  have hqperiod : (∫ y in (0 : ℝ)..T, q y) = 0 := by
    dsimp [q, m]
    rw [intervalIntegral.integral_sub
      (hcont.intervalIntegrable 0 T)
      (continuous_const.intervalIntegrable 0 T)]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, smul_eq_mul]
    field_simp [hT.ne']
    ring
  have hPcont : Continuous P :=
    intervalIntegral.continuous_primitive hqint 0
  have hPper : Function.Periodic P T := by
    intro x
    dsimp only [P]
    rw [hqper.intervalIntegral_add_eq_add 0 x hqint]
    simp [hqperiod]
  obtain ⟨C, hC⟩ :=
    (hPper.isBounded_of_continuous hT.ne' hPcont).exists_norm_le
  have hPbound : ∀ x : ℝ, ‖P x‖ ≤ C := by
    intro x
    exact hC (P x) ⟨x, rfl⟩
  have hC0 : 0 ≤ C := by
    exact (norm_nonneg (P 0)).trans (hPbound 0)
  have hqbounded :=
    hqper.isBounded_of_continuous hT.ne' hqcont
  obtain ⟨D, hD⟩ := hqbounded.exists_norm_le
  have hqbound : ∀ x : ℝ, ‖q x‖ ≤ D := by
    intro x
    exact hD (q x) ⟨x, rfl⟩
  have hqmean :
      Tendsto (realAbelMean q) (𝓝[>] 0) (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero'
    · filter_upwards [self_mem_nhdsWithin] with a ha
      exact norm_nonneg (realAbelMean q a)
    · filter_upwards [self_mem_nhdsWithin] with a ha
      have haPos : 0 < a := ha
      let e : ℝ → ℝ := fun y => Real.exp (-a * y)
      have hecont : Continuous e := by
        fun_prop
      have heint : IntegrableOn e (Set.Ioi 0) := by
        simpa [e] using integrableOn_exp_neg_mul_Ioi haPos
      have hPeint : IntegrableOn (fun y => P y * e y) (Set.Ioi 0) := by
        simpa [mul_comm] using
          heint.mul_bdd hPcont.aestronglyMeasurable
            (by filter_upwards [] with y; exact hPbound y)
      have hqeint : IntegrableOn (fun y => q y * e y) (Set.Ioi 0) := by
        simpa [mul_comm] using
          heint.mul_bdd hqcont.aestronglyMeasurable
            (by filter_upwards [] with y; exact hqbound y)
      have hPderiv :
          ∀ y ∈ Set.Ioi (0 : ℝ), HasDerivAt P (q y) y := by
        intro y _hy
        exact intervalIntegral.integral_hasDerivAt_right
          (hqcont.intervalIntegrable 0 y)
          hqcont.aestronglyMeasurable.stronglyMeasurableAtFilter
          hqcont.continuousAt
      have hederiv :
          ∀ y ∈ Set.Ioi (0 : ℝ),
            HasDerivAt e (-a * e y) y := by
        intro y _hy
        dsimp only [e]
        convert
          (Real.hasDerivAt_exp (-a * y)).comp y
            ((hasDerivAt_const y (-a)).mul (hasDerivAt_id y)) using 1 <;>
          ring
      have hzero :
          Tendsto (P * e) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
        have hprod : ContinuousAt (P * e) 0 :=
          hPcont.continuousAt.mul hecont.continuousAt
        simpa [P, e] using hprod.tendsto.mono_left nhdsWithin_le_nhds
      have hinfty :
          Tendsto (P * e) atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        apply squeeze_zero'
        · filter_upwards [] with y
          exact norm_nonneg ((P * e) y)
        · filter_upwards [] with y
          change ‖P y * e y‖ ≤ C * e y
          simp only [e, norm_mul, Real.norm_eq_abs,
            abs_of_pos (Real.exp_pos _)]
          exact mul_le_mul_of_nonneg_right (hPbound y) (Real.exp_pos _).le
        · simpa [e] using
            (tendsto_exp_neg_mul_atTop_zero haPos).const_mul C
      have hparts :=
        integral_Ioi_mul_deriv_eq_deriv_mul
          hPderiv hederiv
          (by
            change
              Integrable
                (fun y => P y * (-a * e y))
                (volume.restrict (Set.Ioi 0))
            convert hPeint.const_mul (-a) using 1
            ext y
            ring)
          (by simpa [Pi.mul_apply, mul_comm] using hqeint)
          hzero hinfty
      have hidentity :
          (∫ y in Set.Ioi (0 : ℝ), q y * e y) =
            a * ∫ y in Set.Ioi (0 : ℝ), P y * e y := by
        rw [show
            (∫ y in Set.Ioi (0 : ℝ), P y * (-a * e y)) =
              -a * ∫ y in Set.Ioi (0 : ℝ), P y * e y by
              rw [← integral_const_mul]
              apply integral_congr_ae
              filter_upwards [] with y
              ring] at hparts
        linarith
      show ‖realAbelMean q a‖ ≤ C * a
      rw [realAbelMean]
      change
        ‖a * ∫ y in Set.Ioi (0 : ℝ),
          Real.exp (-a * y) * q y‖ ≤ C * a
      have hidentity' :
          (∫ y in Set.Ioi (0 : ℝ),
              Real.exp (-a * y) * q y) =
            a * ∫ y in Set.Ioi (0 : ℝ),
              P y * Real.exp (-a * y) := by
        simpa [e, mul_comm] using hidentity
      rw [hidentity']
      simp only [norm_mul, Real.norm_eq_abs, abs_of_pos haPos]
      have hnorm :
          ‖∫ y in Set.Ioi (0 : ℝ), P y * e y‖ ≤
            C * (1 / a) := by
        calc
          ‖∫ y in Set.Ioi (0 : ℝ), P y * e y‖ ≤
              ∫ y in Set.Ioi (0 : ℝ), ‖P y * e y‖ :=
            norm_integral_le_integral_norm _
          _ ≤ ∫ y in Set.Ioi (0 : ℝ), C * e y := by
            apply integral_mono hPeint.norm (heint.const_mul C)
            intro y
            simp only [e, norm_mul, Real.norm_eq_abs,
              abs_of_pos (Real.exp_pos _)]
            exact mul_le_mul_of_nonneg_right
              (hPbound y) (Real.exp_pos _).le
          _ = C * (1 / a) := by
            rw [integral_const_mul]
            rw [show
              (∫ y in Set.Ioi (0 : ℝ), e y) = 1 / a by
                simpa [e] using integral_exp_neg_mul_Ioi haPos]
      calc
        a * (a * ‖∫ y in Set.Ioi (0 : ℝ),
            P y * Real.exp (-a * y)‖) ≤ a * (a * (C * (1 / a))) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hnorm haPos.le) haPos.le
        _ = C * a := by field_simp [haPos.ne']
    · have ha0 :
          Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      simpa using ha0.const_mul C
  have hdecomp :
      ∀ᶠ a : ℝ in 𝓝[>] 0,
        realAbelMean f a = realAbelMean q a + m := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have haPos : 0 < a := ha
    rw [realAbelMean, realAbelMean]
    have hpoint :
        (fun y : ℝ => Real.exp (-a * y) * f y) =
          (fun y : ℝ => Real.exp (-a * y) * q y) +
            (fun y : ℝ => Real.exp (-a * y) * m) := by
      funext y
      dsimp [q]
      ring
    have hqweighted :
        IntegrableOn (fun y : ℝ => Real.exp (-a * y) * q y)
          (Set.Ioi 0) :=
      (integrableOn_exp_neg_mul_Ioi haPos).mul_bdd
        hqcont.aestronglyMeasurable
        (by filter_upwards [] with y; exact hqbound y)
    have hmweighted :
        IntegrableOn (fun y : ℝ => Real.exp (-a * y) * m)
          (Set.Ioi 0) :=
      (integrableOn_exp_neg_mul_Ioi haPos).mul_const m
    rw [hpoint]
    change
      a * (∫ y in Set.Ioi (0 : ℝ),
        (Real.exp (-a * y) * q y +
          Real.exp (-a * y) * m)) =
        a * (∫ y in Set.Ioi (0 : ℝ),
          Real.exp (-a * y) * q y) + m
    rw [integral_add hqweighted hmweighted]
    rw [integral_mul_const, integral_exp_neg_mul_Ioi haPos]
    field_simp [haPos.ne']
  have hlimit :
      Tendsto (fun a => realAbelMean q a + m)
        (𝓝[>] 0) (𝓝 (0 + m)) :=
    hqmean.add tendsto_const_nhds
  simpa [m] using
    hlimit.congr' (Filter.EventuallyEq.symm hdecomp)

/-- The elementary multiple-angle estimate used to keep the two-frequency
dual kernel in the same sign chamber as its first harmonic. -/
lemma abs_sin_nat_mul_le (n : ℕ) (x : ℝ) :
    |Real.sin ((n : ℝ) * x)| ≤ (n : ℝ) * |Real.sin x| := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Nat.cast_succ, add_mul, Real.sin_add]
      simp only [one_mul]
      calc
        |Real.sin ((n : ℝ) * x) * Real.cos x +
            Real.cos ((n : ℝ) * x) * Real.sin x| ≤
            |Real.sin ((n : ℝ) * x) * Real.cos x| +
              |Real.cos ((n : ℝ) * x) * Real.sin x| :=
          abs_add_le _ _
        _ = |Real.sin ((n : ℝ) * x)| * |Real.cos x| +
            |Real.cos ((n : ℝ) * x)| * |Real.sin x| := by
          rw [abs_mul, abs_mul]
        _ ≤ ((n : ℝ) * |Real.sin x|) * 1 +
            1 * |Real.sin x| := by
          gcongr
          · exact Real.abs_cos_le_one x
          · exact Real.abs_cos_le_one ((n : ℝ) * x)
        _ = ((n : ℝ) + 1) * |Real.sin x| := by ring

/-- For an odd multiplier, the corresponding cosine is pointwise dominated
by the first cosine times the multiplier. -/
theorem abs_cos_odd_mul_le (k : ℕ) (theta : ℝ) :
    |Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)| ≤
      ((2 * k + 1 : ℕ) : ℝ) * |Real.cos theta| := by
  let n : ℕ := 2 * k + 1
  have hmultiple :=
    abs_sin_nat_mul_le n (theta - Real.pi / 2)
  have hleft :
      |Real.sin ((n : ℝ) * (theta - Real.pi / 2))| =
        |Real.cos ((n : ℝ) * theta)| := by
    have hangle :
        (n : ℝ) * (theta - Real.pi / 2) =
          ((n : ℝ) * theta - Real.pi / 2) -
            (k : ℝ) * Real.pi := by
      dsimp [n]
      push_cast
      ring
    rw [hangle, Real.sin_sub_nat_mul_pi,
      Real.sin_sub_pi_div_two]
    simp
  have hright :
      |Real.sin (theta - Real.pi / 2)| =
        |Real.cos theta| := by
    rw [Real.sin_sub_pi_div_two, abs_neg]
  rw [hleft, hright] at hmultiple
  simpa [n] using hmultiple

/-- The square-wave phase of the first cosine.  Its value at the zeros of
`cos` is immaterial for integration and is chosen to be `1`. -/
def oddCosPhase (theta : ℝ) : ℝ :=
  if Real.cos theta < 0 then -1 else 1

/-- The strengthened two-frequency dual kernel.  The perturbation
`1 / (2n)` is small enough that the kernel never changes the sign of its
first harmonic, while its missing `n`-th coefficient lowers the exact
periodic `L¹` norm. -/
def missingOddHarmonicKernel (k : ℕ) (theta : ℝ) : ℝ :=
  Real.cos theta -
    ((-1 : ℝ) ^ k) *
      (1 / (2 * ((2 * k + 1 : ℕ) : ℝ))) *
        Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)

private lemma abs_sub_eq_abs_sub_phase_mul_of_abs_le_half
    {u v : ℝ} (hv : |v| ≤ |u| / 2) :
    |u - v| =
      |u| - (if u < 0 then -1 else 1) * v := by
  by_cases hu : u < 0
  · have habsu : |u| = -u := abs_of_neg hu
    have hvlower : u / 2 ≤ v := by
      have h := neg_le_of_abs_le (by simpa [habsu] using hv)
      linarith
    have hneg : u - v < 0 := by linarith
    rw [if_pos hu, abs_of_neg hneg, habsu]
    ring
  · have hu0 : 0 ≤ u := le_of_not_gt hu
    have habsu : |u| = u := abs_of_nonneg hu0
    have hvupper : v ≤ u / 2 := by
      exact (le_abs_self v).trans (by simpa [habsu] using hv)
    have hnonneg : 0 ≤ u - v := by linarith
    rw [if_neg hu, abs_of_nonneg hnonneg, habsu]
    ring

theorem abs_missingOddHarmonicKernel_eq (k : ℕ) (theta : ℝ) :
    |missingOddHarmonicKernel k theta| =
      |Real.cos theta| -
        oddCosPhase theta *
          (((-1 : ℝ) ^ k) *
            (1 / (2 * ((2 * k + 1 : ℕ) : ℝ))) *
              Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)) := by
  let n : ℕ := 2 * k + 1
  let v : ℝ :=
    ((-1 : ℝ) ^ k) * (1 / (2 * (n : ℝ))) *
      Real.cos ((n : ℝ) * theta)
  have hn : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  have heps : |(-1 : ℝ) ^ k| = 1 := by simp
  have hv :
      |v| ≤ |Real.cos theta| / 2 := by
    rw [show |v| =
        (1 / (2 * (n : ℝ))) *
          |Real.cos ((n : ℝ) * theta)| by
      dsimp [v]
      rw [abs_mul, abs_mul, heps, one_mul,
        abs_of_pos (by positivity :
          0 < (1 / (2 * (n : ℝ)) : ℝ))]
      ]
    calc
      (1 / (2 * (n : ℝ))) *
          |Real.cos ((n : ℝ) * theta)| ≤
          (1 / (2 * (n : ℝ))) *
            ((n : ℝ) * |Real.cos theta|) := by
        exact mul_le_mul_of_nonneg_left
          (by simpa [n] using abs_cos_odd_mul_le k theta)
          (by positivity)
      _ = |Real.cos theta| / 2 := by
        field_simp [hn.ne']
  change
    |Real.cos theta - v| =
      |Real.cos theta| - oddCosPhase theta * v
  simpa [oddCosPhase] using
    abs_sub_eq_abs_sub_phase_mul_of_abs_le_half hv

private lemma integral_cos_real_mul
    {c a b : ℝ} (hc : c ≠ 0) :
    (∫ theta in a..b, Real.cos (c * theta)) =
      (Real.sin (c * b) - Real.sin (c * a)) / c := by
  let F : ℝ → ℝ := fun theta => (1 / c) * Real.sin (c * theta)
  have hderiv :
      ∀ theta ∈ Set.uIcc a b,
        HasDerivAt F (Real.cos (c * theta)) theta := by
    intro theta _htheta
    dsimp [F]
    convert
      ((Real.hasDerivAt_sin (c * theta)).comp theta
        ((hasDerivAt_const theta c).mul (hasDerivAt_id theta))).const_mul
          (1 / c) using 1 <;>
      field_simp [hc] <;>
      ring
  have hint :
      IntervalIntegrable (fun theta => Real.cos (c * theta))
        volume a b := by
    exact
      (Real.continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable a b
  have h :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [h]
  dsimp [F]
  field_simp [hc]

private lemma odd_half_pi_sin (k : ℕ) :
    Real.sin (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
      (-1 : ℝ) ^ k := by
  rw [show
      (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) =
        Real.pi / 2 + (k : ℝ) * Real.pi by
      push_cast
      ring]
  rw [Real.sin_add_nat_mul_pi]
  simp

private lemma three_odd_half_pi_sin (k : ℕ) :
    Real.sin (((2 * k + 1 : ℕ) : ℝ) *
        (Real.pi + Real.pi / 2)) =
      -((-1 : ℝ) ^ k) := by
  rw [show
      (((2 * k + 1 : ℕ) : ℝ) *
          (Real.pi + Real.pi / 2)) =
        (((2 * k + 1 : ℕ) : ℝ) * Real.pi / 2) +
          ((2 * k + 1 : ℕ) : ℝ) * Real.pi by ring]
  rw [Real.sin_add_nat_mul_pi]
  rw [Odd.neg_one_pow (odd_two_mul_add_one k)]
  rw [odd_half_pi_sin]
  ring

private lemma oddCosPhase_mul_cos_intervalIntegrable
    (k : ℕ) (a b : ℝ) :
    IntervalIntegrable
      (fun theta =>
        oddCosPhase theta *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta))
      volume a b := by
  let g : ℝ → ℝ := fun theta =>
    oddCosPhase theta *
      Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)
  have hgmeas : Measurable g := by
    apply Measurable.mul
    · exact Measurable.ite
        (measurableSet_lt Real.continuous_cos.measurable
          measurable_const) measurable_const measurable_const
    · fun_prop
  rw [intervalIntegrable_iff]
  apply volume.integrableOn_of_bounded
    (by simp [Real.volume_uIoc])
    hgmeas.aestronglyMeasurable
  filter_upwards [] with theta
  change ‖g theta‖ ≤ 1
  dsimp [g, oddCosPhase]
  split_ifs <;>
    simp [Real.abs_cos_le_one]

private lemma integral_oddCosPhase_mul_oddCos (k : ℕ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        oddCosPhase theta *
          Real.cos (((2 * k + 1 : ℕ) : ℝ) * theta)) =
      4 * ((-1 : ℝ) ^ k) /
        ((2 * k + 1 : ℕ) : ℝ) := by
  let n : ℕ := 2 * k + 1
  let c : ℝ := (n : ℝ)
  have hnpos : (0 : ℝ) < c := by
    dsimp [c, n]
    positivity
  let g : ℝ → ℝ := fun theta =>
    oddCosPhase theta * Real.cos (c * theta)
  have hfirst :
      (∫ theta in (0 : ℝ)..Real.pi / 2, g theta) =
        ∫ theta in (0 : ℝ)..Real.pi / 2,
          Real.cos (c * theta) := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    rw [Set.uIcc_of_le Real.pi_div_two_pos.le] at htheta
    have hcos : 0 ≤ Real.cos theta := by
      apply Real.cos_nonneg_of_neg_pi_div_two_le_of_le
      · exact (neg_nonpos.mpr Real.pi_div_two_pos.le).trans htheta.1
      · exact htheta.2
    simp [g, oddCosPhase, not_lt.mpr hcos]
  have hmiddle :
      (∫ theta in Real.pi / 2..Real.pi + Real.pi / 2,
          g theta) =
        ∫ theta in Real.pi / 2..Real.pi + Real.pi / 2,
          -Real.cos (c * theta) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [volume.ae_ne (Real.pi / 2),
      volume.ae_ne (Real.pi + Real.pi / 2)] with theta hleft hright
    intro htheta
    have horder : Real.pi / 2 ≤ Real.pi + Real.pi / 2 := by
      linarith [Real.pi_pos]
    rw [Set.uIoc_of_le horder] at htheta
    have hcos : Real.cos theta < 0 :=
      Real.cos_neg_of_pi_div_two_lt_of_lt
        htheta.1
        (lt_of_le_of_ne htheta.2 hright)
    simp [g, oddCosPhase, hcos]
  have hlast :
      (∫ theta in Real.pi + Real.pi / 2..2 * Real.pi,
          g theta) =
        ∫ theta in Real.pi + Real.pi / 2..2 * Real.pi,
          Real.cos (c * theta) := by
    apply intervalIntegral.integral_congr
    intro theta htheta
    have horder :
        Real.pi + Real.pi / 2 ≤ 2 * Real.pi := by
      linarith [Real.pi_pos]
    rw [Set.uIcc_of_le horder] at htheta
    have hshift :
        -(Real.pi / 2) ≤ theta - 2 * Real.pi ∧
          theta - 2 * Real.pi ≤ Real.pi / 2 := by
      constructor <;> linarith [htheta.1, htheta.2, Real.pi_pos]
    have hcosShift :
        0 ≤ Real.cos (theta - 2 * Real.pi) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le hshift.1 hshift.2
    have hcos : 0 ≤ Real.cos theta := by
      simpa [Real.cos_sub_two_pi] using hcosShift
    simp [g, oddCosPhase, not_lt.mpr hcos]
  have hg01 : IntervalIntegrable g volume 0 (Real.pi / 2) := by
    simpa [g, c, n] using
      oddCosPhase_mul_cos_intervalIntegrable k 0 (Real.pi / 2)
  have hg12 :
      IntervalIntegrable g volume
        (Real.pi / 2) (Real.pi + Real.pi / 2) := by
    simpa [g, c, n] using
      oddCosPhase_mul_cos_intervalIntegrable k
        (Real.pi / 2) (Real.pi + Real.pi / 2)
  have hg23 :
      IntervalIntegrable g volume
        (Real.pi + Real.pi / 2) (2 * Real.pi) := by
    simpa [g, c, n] using
      oddCosPhase_mul_cos_intervalIntegrable k
        (Real.pi + Real.pi / 2) (2 * Real.pi)
  have hsplit :
      (∫ theta in (0 : ℝ)..2 * Real.pi, g theta) =
        (∫ theta in (0 : ℝ)..Real.pi / 2, g theta) +
          (∫ theta in Real.pi / 2..Real.pi + Real.pi / 2, g theta) +
            ∫ theta in Real.pi + Real.pi / 2..2 * Real.pi, g theta := by
    calc
      (∫ theta in (0 : ℝ)..2 * Real.pi, g theta) =
          (∫ theta in (0 : ℝ)..Real.pi + Real.pi / 2, g theta) +
            ∫ theta in Real.pi + Real.pi / 2..2 * Real.pi, g theta := by
        rw [intervalIntegral.integral_add_adjacent_intervals
          (hg01.trans hg12) hg23]
      _ =
          ((∫ theta in (0 : ℝ)..Real.pi / 2, g theta) +
            ∫ theta in Real.pi / 2..Real.pi + Real.pi / 2, g theta) +
              ∫ theta in Real.pi + Real.pi / 2..2 * Real.pi, g theta := by
        rw [intervalIntegral.integral_add_adjacent_intervals hg01 hg12]
  rw [hsplit, hfirst, hmiddle, hlast]
  rw [intervalIntegral.integral_neg]
  rw [integral_cos_real_mul hnpos.ne',
    integral_cos_real_mul hnpos.ne',
    integral_cos_real_mul hnpos.ne']
  have hsin0 : Real.sin (c * 0) = 0 := by simp
  have hsin1 :
      Real.sin (c * (Real.pi / 2)) = (-1 : ℝ) ^ k := by
    simpa [c, n, mul_div_assoc] using odd_half_pi_sin k
  have hsin2 :
      Real.sin (c * (Real.pi + Real.pi / 2)) =
        -((-1 : ℝ) ^ k) := by
    simpa [c, n] using three_odd_half_pi_sin k
  have hsin3 : Real.sin (c * (2 * Real.pi)) = 0 := by
    rw [show c * (2 * Real.pi) = ((2 * n : ℕ) : ℝ) * Real.pi by
      dsimp [c]
      push_cast
      ring]
    exact Real.sin_nat_mul_pi (2 * n)
  rw [hsin0, hsin1, hsin2, hsin3]
  dsimp [c, n]
  ring

private lemma oddCosPhase_mul_cos_eq_abs_cos (theta : ℝ) :
    oddCosPhase theta * Real.cos theta = |Real.cos theta| := by
  by_cases hcos : Real.cos theta < 0
  · simp [oddCosPhase, hcos, abs_of_neg hcos]
  · have hcos0 : 0 ≤ Real.cos theta := le_of_not_gt hcos
    simp [oddCosPhase, hcos, abs_of_nonneg hcos0]

private lemma integral_abs_cos_zero_two_pi :
    (∫ theta in (0 : ℝ)..2 * Real.pi, |Real.cos theta|) = 4 := by
  calc
    (∫ theta in (0 : ℝ)..2 * Real.pi, |Real.cos theta|) =
        ∫ theta in (0 : ℝ)..2 * Real.pi,
          oddCosPhase theta * Real.cos theta := by
      apply intervalIntegral.integral_congr
      intro theta _htheta
      exact (oddCosPhase_mul_cos_eq_abs_cos theta).symm
    _ = 4 := by
      simpa using integral_oddCosPhase_mul_oddCos 0

/-- Exact strengthened `L¹` certificate. -/
theorem integral_abs_missingOddHarmonicKernel (k : ℕ) :
    (∫ theta in (0 : ℝ)..2 * Real.pi,
        |missingOddHarmonicKernel k theta|) =
      4 - 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2) := by
  let n : ℕ := 2 * k + 1
  let epsilon : ℝ := (-1 : ℝ) ^ k
  let t : ℝ := 1 / (2 * (n : ℝ))
  have hphaseInt :=
    oddCosPhase_mul_cos_intervalIntegrable k 0 (2 * Real.pi)
  rw [show
      (fun theta => |missingOddHarmonicKernel k theta|) =
        (fun theta => |Real.cos theta|) -
          fun theta =>
            oddCosPhase theta *
              (epsilon * t *
                Real.cos ((n : ℝ) * theta)) by
      funext theta
      simpa [epsilon, t, n] using
        abs_missingOddHarmonicKernel_eq k theta]
  change
    (∫ theta in (0 : ℝ)..2 * Real.pi,
      |Real.cos theta| -
        oddCosPhase theta *
          (epsilon * t * Real.cos ((n : ℝ) * theta))) =
      4 - 2 / (((2 * k + 1 : ℕ) : ℝ) ^ 2)
  rw [intervalIntegral.integral_sub
    (Real.continuous_cos.abs.intervalIntegrable 0 (2 * Real.pi))
    (by
      convert hphaseInt.const_mul (epsilon * t) using 1
      ext theta
      dsimp [epsilon, t, n]
      ring)]
  rw [integral_abs_cos_zero_two_pi]
  have hcoeff := integral_oddCosPhase_mul_oddCos k
  rw [show
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        oddCosPhase theta *
          (epsilon * t * Real.cos ((n : ℝ) * theta))) =
        epsilon * t *
          (∫ theta in (0 : ℝ)..2 * Real.pi,
            oddCosPhase theta *
              Real.cos ((n : ℝ) * theta)) by
      rw [← intervalIntegral.integral_const_mul]
      apply intervalIntegral.integral_congr
      intro theta _htheta
      ring]
  rw [show
      (∫ theta in (0 : ℝ)..2 * Real.pi,
        oddCosPhase theta * Real.cos ((n : ℝ) * theta)) =
          4 * epsilon / (n : ℝ) by
      simpa [epsilon, n] using hcoeff]
  have hepsilon_sq : epsilon * epsilon = 1 := by
    dsimp [epsilon]
    rw [← pow_add]
    simp
  have hnpos : (0 : ℝ) < n := by
    exact_mod_cast (show 0 < n by omega)
  dsimp [t]
  rw [mul_div_assoc]
  field_simp [hnpos.ne']
  nlinarith

/-- Denominator produced by the strengthened sign-preserving certificate. -/
def sharpenedMissingHarmonicDenominator (k : ℕ) : ℝ :=
  2 / Real.pi -
    1 / (Real.pi * (((2 * k + 1 : ℕ) : ℝ) ^ 2))

/-- Oscillation lower bound produced by the strengthened certificate. -/
def sharpenedMissingHarmonicLowerBound (k : ℕ) : ℝ :=
  1 / sharpenedMissingHarmonicDenominator k

theorem sharpenedMissingHarmonicDenominator_pos (k : ℕ) :
    0 < sharpenedMissingHarmonicDenominator k := by
  have hn : (1 : ℝ) ≤ ((2 * k + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ 2 * k + 1 by omega)
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold sharpenedMissingHarmonicDenominator
  rw [sub_pos, div_lt_div_iff₀
    (mul_pos hpi (sq_pos_of_pos (zero_lt_one.trans_le hn))) hpi]
  nlinarith [sq_nonneg (((2 * k + 1 : ℕ) : ℝ) - 1)]

theorem sharpenedMissingHarmonicDenominator_lt_two_div_pi (k : ℕ) :
    sharpenedMissingHarmonicDenominator k < 2 / Real.pi := by
  have hn : (0 : ℝ) < ((2 * k + 1 : ℕ) : ℝ) := by positivity
  have hterm :
      0 < 1 /
        (Real.pi * (((2 * k + 1 : ℕ) : ℝ) ^ 2)) := by
    positivity
  unfold sharpenedMissingHarmonicDenominator
  linarith

theorem pi_div_two_lt_sharpenedMissingHarmonicLowerBound (k : ℕ) :
    Real.pi / 2 < sharpenedMissingHarmonicLowerBound k := by
  have hdenpos := sharpenedMissingHarmonicDenominator_pos k
  have hdenlt := sharpenedMissingHarmonicDenominator_lt_two_div_pi k
  calc
    Real.pi / 2 = 1 / (2 / Real.pi) := by
      field_simp [Real.pi_ne_zero]
    _ < 1 / sharpenedMissingHarmonicDenominator k :=
      one_div_lt_one_div_of_lt hdenpos hdenlt
    _ = sharpenedMissingHarmonicLowerBound k := rfl

/-- A global pointwise bound passes to Abel limits after testing against an
integrable real kernel. -/
theorem abs_limit_realAbelMean_mul_le_of_global_bound
    {h q : ℝ → ℝ} {K Q D : ℝ}
    (hbound : ∀ y ∈ Set.Ioi (0 : ℝ), |h y| ≤ K)
    (hqint : ∀ a : ℝ, 0 < a →
      IntegrableOn
        (fun y => Real.exp (-a * y) * |q y|)
        (Set.Ioi 0))
    (hlim : Tendsto (realAbelMean (fun y => h y * q y))
      (𝓝[>] 0) (𝓝 Q))
    (hqlim : Tendsto (realAbelMean (fun y => |q y|))
      (𝓝[>] 0) (𝓝 D)) :
    |Q| ≤ K * D := by
  have hEventually :
      (fun a => |realAbelMean (fun y => h y * q y) a|) ≤ᶠ[𝓝[>] 0]
        (fun a => K * realAbelMean (fun y => |q y|) a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have haPos : 0 < a := ha
    have hdom :
        ‖∫ y : ℝ in Set.Ioi 0,
            Real.exp (-a * y) * (h y * q y)‖ ≤
          ∫ y : ℝ in Set.Ioi 0,
            K * (Real.exp (-a * y) * |q y|) := by
      apply norm_integral_le_of_norm_le ((hqint a haPos).const_mul K)
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
      rw [Real.norm_eq_abs, abs_mul, abs_mul,
        abs_of_nonneg (Real.exp_nonneg _)]
      calc
        Real.exp (-a * y) * (|h y| * |q y|) ≤
            Real.exp (-a * y) * (K * |q y|) := by
          gcongr
          exact hbound y hy
        _ = K * (Real.exp (-a * y) * |q y|) := by ring
    rw [realAbelMean, realAbelMean, abs_mul, abs_of_pos haPos]
    calc
      a * ‖∫ y : ℝ in Set.Ioi 0,
          Real.exp (-a * y) * (h y * q y)‖ ≤
          a * ∫ y : ℝ in Set.Ioi 0,
            K * (Real.exp (-a * y) * |q y|) :=
        mul_le_mul_of_nonneg_left hdom haPos.le
      _ = K * (a * ∫ y : ℝ in Set.Ioi 0,
          Real.exp (-a * y) * |q y|) := by
        rw [MeasureTheory.integral_const_mul]
        ring
  exact le_of_tendsto_of_tendsto hlim.abs
    (hqlim.const_mul K) hEventually

/-- An eventual tail bound gives the same Abel-limit inequality: the
integrable finite prefix has Abel mass tending to zero. -/
theorem abs_limit_realAbelMean_mul_le_of_tail_bound
    {h q : ℝ → ℝ} {K Q D Y : ℝ}
    (hK : 0 ≤ K) (hY : 0 ≤ Y)
    (hbound : ∀ y ∈ Set.Ioi Y, |h y| ≤ K)
    (hprefix : IntegrableOn
      (fun y => h y * q y) (Set.Ioc 0 Y))
    (hint : ∀ a : ℝ, 0 < a →
      IntegrableOn
        (fun y => Real.exp (-a * y) * (h y * q y))
        (Set.Ioi 0))
    (hqint : ∀ a : ℝ, 0 < a →
      IntegrableOn
        (fun y => Real.exp (-a * y) * |q y|)
        (Set.Ioi 0))
    (hlim : Tendsto (realAbelMean (fun y => h y * q y))
      (𝓝[>] 0) (𝓝 Q))
    (hqlim : Tendsto (realAbelMean (fun y => |q y|))
      (𝓝[>] 0) (𝓝 D)) :
    |Q| ≤ K * D := by
  let C : ℝ := ∫ y in Set.Ioc (0 : ℝ) Y, |h y * q y|
  have hC0 : 0 ≤ C := by
    dsimp only [C]
    exact integral_nonneg fun _ => abs_nonneg _
  have hEventually :
      (fun a => |realAbelMean (fun y => h y * q y) a|) ≤ᶠ[𝓝[>] 0]
        (fun a => a * C + K * realAbelMean (fun y => |q y|) a) := by
    filter_upwards [self_mem_nhdsWithin] with a ha
    have haPos : 0 < a := ha
    let r : ℝ → ℝ := fun y =>
      Real.exp (-a * y) * (h y * q y)
    let w : ℝ → ℝ := fun y =>
      Real.exp (-a * y) * |q y|
    have hrFull : IntegrableOn r (Set.Ioi 0) := by
      simpa only [r] using hint a haPos
    have hrPrefix : IntegrableOn r (Set.Ioc 0 Y) :=
      hrFull.mono_set Set.Ioc_subset_Ioi_self
    have hrTail : IntegrableOn r (Set.Ioi Y) :=
      hrFull.mono_set (Set.Ioi_subset_Ioi hY)
    have hwFull : IntegrableOn w (Set.Ioi 0) := by
      simpa only [w] using hqint a haPos
    have hwTail : IntegrableOn w (Set.Ioi Y) :=
      hwFull.mono_set (Set.Ioi_subset_Ioi hY)
    have hsplit :
        (∫ y in Set.Ioi (0 : ℝ), r y) =
          (∫ y in Set.Ioc (0 : ℝ) Y, r y) +
            ∫ y in Set.Ioi Y, r y := by
      rw [← Set.Ioc_union_Ioi_eq_Ioi hY,
        MeasureTheory.setIntegral_union Set.Ioc_disjoint_Ioi_same
          measurableSet_Ioi hrPrefix hrTail]
    have hprefixNorm :
        ‖∫ y in Set.Ioc (0 : ℝ) Y, r y‖ ≤ C := by
      apply norm_integral_le_of_norm_le hprefix.norm
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
      have hy0 : 0 ≤ y := hy.1.le
      have hexpLe : Real.exp (-a * y) ≤ 1 := by
        rw [Real.exp_le_one_iff]
        exact mul_nonpos_of_nonpos_of_nonneg
          (neg_nonpos.mpr haPos.le) hy0
      dsimp only [r, C]
      rw [Real.norm_eq_abs, abs_mul,
        abs_of_pos (Real.exp_pos _)]
      exact mul_le_of_le_one_left (abs_nonneg _) hexpLe
    have htailNorm :
        ‖∫ y in Set.Ioi Y, r y‖ ≤
          K * ∫ y in Set.Ioi (0 : ℝ), w y := by
      have hdom :
          ‖∫ y in Set.Ioi Y, r y‖ ≤
            ∫ y in Set.Ioi Y, K * w y := by
        apply norm_integral_le_of_norm_le (hwTail.const_mul K)
        filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
        dsimp only [r, w]
        rw [Real.norm_eq_abs, abs_mul, abs_mul,
          abs_of_pos (Real.exp_pos _)]
        calc
          Real.exp (-a * y) * (|h y| * |q y|) ≤
              Real.exp (-a * y) * (K * |q y|) := by
            gcongr
            exact hbound y hy
          _ = K * (Real.exp (-a * y) * |q y|) := by ring
      have hwNonneg :
          0 ≤ᵐ[volume.restrict (Set.Ioi 0)] w :=
        ae_of_all _ fun y => by
          dsimp only [w]
          positivity
      have htailLe :
          (∫ y in Set.Ioi Y, w y) ≤
            ∫ y in Set.Ioi (0 : ℝ), w y :=
        setIntegral_mono_set hwFull hwNonneg
          (Set.Ioi_subset_Ioi hY).eventuallyLE
      calc
        ‖∫ y in Set.Ioi Y, r y‖ ≤
            ∫ y in Set.Ioi Y, K * w y := hdom
        _ = K * ∫ y in Set.Ioi Y, w y := by
          rw [MeasureTheory.integral_const_mul]
        _ ≤ K * ∫ y in Set.Ioi (0 : ℝ), w y :=
          mul_le_mul_of_nonneg_left htailLe hK
    rw [realAbelMean, realAbelMean, abs_mul, abs_of_pos haPos]
    change
      a * ‖∫ y in Set.Ioi (0 : ℝ), r y‖ ≤
        a * C + K * (a * ∫ y in Set.Ioi (0 : ℝ), w y)
    rw [hsplit]
    calc
      a * ‖(∫ y in Set.Ioc (0 : ℝ) Y, r y) +
          ∫ y in Set.Ioi Y, r y‖ ≤
          a * (‖∫ y in Set.Ioc (0 : ℝ) Y, r y‖ +
            ‖∫ y in Set.Ioi Y, r y‖) := by
        gcongr
        exact norm_add_le _ _
      _ ≤ a * (C + K * ∫ y in Set.Ioi (0 : ℝ), w y) := by
        gcongr
      _ = a * C + K * (a * ∫ y in Set.Ioi (0 : ℝ), w y) := by
        ring
  have haC :
      Tendsto (fun a : ℝ => a * C) (𝓝[>] 0) (𝓝 0) := by
    have ha0 :
        Tendsto (fun a : ℝ => a) (𝓝[>] 0) (𝓝 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa using ha0.mul_const C
  exact le_of_tendsto_of_tendsto hlim.abs
    (by simpa only [zero_add] using
      haC.add (hqlim.const_mul K)) hEventually

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
