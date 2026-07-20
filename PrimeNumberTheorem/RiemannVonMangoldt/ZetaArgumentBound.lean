import PrimeNumberTheorem.CentralHorizontalEdge
import MathlibAux.HorizontalArgument

open Complex MeasureTheory Set Topology
open scoped BigOperators Interval

namespace PrimeNumberTheorem
namespace RiemannVonMangoldt

/-- The zeta divisor in the shifted Jensen disk used to control the horizontal
argument variation at height `T`. -/
noncomputable def shiftedZetaDivisor (T : ℝ) : ℂ → ℤ :=
  MeromorphicOn.divisor riemannZeta
    (Metric.closedBall ((3 / 2 : ℂ) + I * T) (7 / 5 : ℝ))

/-- The finite principal-part sum supplied by shifted Jensen at height `T`. -/
noncomputable def shiftedDivisorPrincipalPart (T sigma : ℝ) : ℂ :=
  ∑ᶠ u, (shiftedZetaDivisor T u : ℂ) *
    ((((sigma : ℂ) + I * T) - u)⁻¹)

/-- At a good height, the integrated imaginary part of the shifted Jensen
principal part is at most `pi` times its total divisor mass. -/
theorem abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass
    {T : ℝ} (hT : 4 ≤ T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    |∫ sigma in (1 / 2 : ℝ)..2,
      (shiftedDivisorPrincipalPart T sigma).im| ≤
      Real.pi * ∑ᶠ u, (shiftedZetaDivisor T u : ℝ) := by
  classical
  let c : ℂ := (3 / 2 : ℂ) + I * T
  let D := shiftedZetaDivisor T
  have hfinite : D.support.Finite := by
    dsimp [D, shiftedZetaDivisor]
    exact (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall c (7 / 5 : ℝ))).finiteSupport
        (isCompact_closedBall c (7 / 5 : ℝ))
  let S : Finset ℂ := hfinite.toFinset
  have hTnonneg : 0 ≤ T := by linarith
  have hT_abs : 4 ≤ |T| := by simpa [abs_of_nonneg hTnonneg] using hT
  have havoid : ∀ u : ℂ,
      u ∈ Metric.closedBall c (7 / 5 : ℝ) → u ≠ 1 := by
    intro u hu
    exact ZeroFreeRegion.closedBall_sigma_it_ne_one_of_height_add_le
      (z := u) (σ := (3 / 2 : ℝ)) (t := T) (R := (7 / 5 : ℝ))
      (H := |T| - 7 / 5) (by simpa [c] using hu) (by linarith) (by linarith)
  have hD : ∀ u, 0 ≤ D u := by
    simpa [D, shiftedZetaDivisor, c] using
      (ZeroFreeRegion.divisor_riemannZeta_closedBall_nonneg havoid)
  have hheight : ∀ u ∈ S, T ≠ u.im := by
    intro u hu hEq
    have huSupport : u ∈ D.support := hfinite.mem_toFinset.mp hu
    have huZero : RiemannHypothesis.IsNontrivialZero u := by
      exact ExplicitFormulaResidues.isNontrivialZero_of_mem_shifted_divisor_support
        hT_abs (by simpa [D, shiftedZetaDivisor, c] using huSupport)
    apply hgood u huZero
    rw [← hEq, abs_of_nonneg hTnonneg]
  have hsummandSupport (sigma : ℝ) :
      (fun u : ℂ => (D u : ℂ) *
        ((((sigma : ℂ) + I * T) - u)⁻¹)).support ⊆ S := by
    intro u hu
    apply hfinite.mem_toFinset.mpr
    by_contra hDu
    have hDuZero : D u = 0 := by
      simpa [Function.mem_support] using hDu
    exact hu (by simp [hDuZero])
  have hprincipal (sigma : ℝ) :
      shiftedDivisorPrincipalPart T sigma =
        ∑ u ∈ S, (D u : ℂ) *
          ((((sigma : ℂ) + I * T) - u)⁻¹) := by
    rw [shiftedDivisorPrincipalPart]
    simpa [D] using
      (finsum_eq_sum_of_support_subset
        (fun u : ℂ => (D u : ℂ) *
          ((((sigma : ℂ) + I * T) - u)⁻¹))
        (hsummandSupport sigma))
  have hne (u : ℂ) (hu : u ∈ S) (sigma : ℝ) :
      ((sigma : ℂ) + I * T) - u ≠ 0 := by
    intro hz
    have him : T - u.im = 0 := by
      simpa using congrArg Complex.im hz
    exact hheight u hu (sub_eq_zero.mp him)
  have hint (u : ℂ) (hu : u ∈ S) :
      IntervalIntegrable
        (fun sigma : ℝ => (D u : ℝ) *
          (((((sigma : ℂ) + I * T) - u)⁻¹).im))
        MeasureTheory.volume (1 / 2 : ℝ) 2 := by
    have hinv : Continuous fun sigma : ℝ =>
        ((((sigma : ℂ) + I * T) - u)⁻¹) := by
      exact (by fun_prop : Continuous fun sigma : ℝ =>
        ((sigma : ℂ) + I * T) - u).inv₀ (hne u hu)
    simpa only [Function.comp_apply] using
      ((Complex.continuous_im.comp hinv).const_mul
        (D u : ℝ)).intervalIntegrable (μ := MeasureTheory.volume)
          (1 / 2 : ℝ) 2
  have himag (sigma : ℝ) :
      (shiftedDivisorPrincipalPart T sigma).im =
        ∑ u ∈ S, (D u : ℝ) *
          (((((sigma : ℂ) + I * T) - u)⁻¹).im) := by
    rw [hprincipal]
    simp
  rw [show (fun sigma : ℝ =>
      (shiftedDivisorPrincipalPart T sigma).im) =
        fun sigma : ℝ => ∑ u ∈ S, (D u : ℝ) *
          (((((sigma : ℂ) + I * T) - u)⁻¹).im) by
      funext sigma
      exact himag sigma]
  rw [intervalIntegral.integral_finset_sum hint]
  calc
    |∑ u ∈ S, ∫ sigma in (1 / 2 : ℝ)..2,
        (D u : ℝ) * (((((sigma : ℂ) + I * T) - u)⁻¹).im)| ≤
        ∑ u ∈ S, |∫ sigma in (1 / 2 : ℝ)..2,
          (D u : ℝ) * (((((sigma : ℂ) + I * T) - u)⁻¹).im)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ u ∈ S, (D u : ℝ) *
        |∫ sigma in (1 / 2 : ℝ)..2,
          (((((sigma : ℂ) + I * T) - u)⁻¹).im)| := by
      apply Finset.sum_congr rfl
      intro u hu
      have hDreal : 0 ≤ (D u : ℝ) := by
        exact_mod_cast hD u
      rw [intervalIntegral.integral_const_mul, abs_mul,
        abs_of_nonneg hDreal]
    _ ≤ ∑ u ∈ S, (D u : ℝ) * Real.pi := by
      apply Finset.sum_le_sum
      intro u hu
      have hDreal : 0 ≤ (D u : ℝ) := by
        exact_mod_cast hD u
      exact mul_le_mul_of_nonneg_left
        (MathlibAux.abs_intervalIntegral_im_inv_horizontal_sub_le_pi
          (hheight u hu))
        hDreal
    _ = Real.pi * ∑ᶠ u, (D u : ℝ) := by
      rw [← Finset.sum_mul, mul_comm]
      congr 1
      have hcastSupport : (fun u : ℂ => (D u : ℝ)).support ⊆ S := by
        intro u hu
        apply hfinite.mem_toFinset.mpr
        by_contra hDu
        have hDZero : D u = 0 := by
          simpa [Function.mem_support] using hDu
        have hcastNe : (D u : ℝ) ≠ 0 := by
          simpa [Function.mem_support] using hu
        exact hcastNe (by exact_mod_cast hDZero)
      exact (finsum_eq_sum_of_support_subset _ hcastSupport).symm
    _ = Real.pi * ∑ᶠ u, (shiftedZetaDivisor T u : ℝ) := by
      simp [D]

private theorem intervalIntegrable_logDeriv_im_goodHeight_horizontal
    {T a b : ℝ} (hT : 0 < T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    IntervalIntegrable
      (fun sigma : ℝ =>
        (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im)
      MeasureTheory.volume a b := by
  apply ContinuousOn.intervalIntegrable
  intro sigma _hsigma
  have hzeta : riemannZeta ((sigma : ℂ) + I * T) ≠ 0 :=
    ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
      (T := T) (t := T) (σ := sigma) hT
      (abs_of_pos hT) hgood
  have hs1 : (sigma : ℂ) + I * T ≠ 1 := by
    intro hs
    have him := congrArg Complex.im hs
    simp at him
    linarith
  have han : ContinuousAt (logDeriv riemannZeta)
      ((sigma : ℂ) + I * T) :=
    (ZeroFreeRegion.analyticAt_logDeriv_riemannZeta_of_ne_one_of_ne_zero
      ((sigma : ℂ) + I * T) hs1 hzeta).continuousAt
  have hmap : ContinuousAt (fun r : ℝ => ((r : ℂ) + I * T)) sigma := by
    fun_prop
  change ContinuousWithinAt
    ((fun z : ℂ => (logDeriv riemannZeta z).im) ∘
      fun r : ℝ => ((r : ℂ) + I * T)) _ sigma
  have hlogMap : ContinuousAt
      (fun r : ℝ => logDeriv riemannZeta ((r : ℂ) + I * T)) sigma :=
    han.comp_of_eq hmap rfl
  have himMap : ContinuousAt
      (fun r : ℝ => (logDeriv riemannZeta ((r : ℂ) + I * T)).im) sigma :=
    Complex.continuous_im.continuousAt.comp_of_eq hlogMap rfl
  exact himMap.continuousWithinAt

private theorem intervalIntegrable_shiftedDivisorPrincipalPart_im
    {T a b : ℝ} (hT : 4 ≤ T)
    (hgood : ExplicitFormulaAux.goodHeight T) :
    IntervalIntegrable
      (fun sigma : ℝ => (shiftedDivisorPrincipalPart T sigma).im)
      MeasureTheory.volume a b := by
  classical
  let c : ℂ := (3 / 2 : ℂ) + I * T
  let D := shiftedZetaDivisor T
  have hfinite : D.support.Finite := by
    dsimp [D, shiftedZetaDivisor]
    exact (MeromorphicOn.divisor riemannZeta
      (Metric.closedBall c (7 / 5 : ℝ))).finiteSupport
        (isCompact_closedBall c (7 / 5 : ℝ))
  let S : Finset ℂ := hfinite.toFinset
  have hTnonneg : 0 ≤ T := by linarith
  have hT_abs : 4 ≤ |T| := by simpa [abs_of_nonneg hTnonneg] using hT
  have hheight : ∀ u ∈ S, T ≠ u.im := by
    intro u hu hEq
    have huSupport : u ∈ D.support := hfinite.mem_toFinset.mp hu
    have huZero : RiemannHypothesis.IsNontrivialZero u := by
      exact ExplicitFormulaResidues.isNontrivialZero_of_mem_shifted_divisor_support
        hT_abs (by simpa [D, shiftedZetaDivisor, c] using huSupport)
    apply hgood u huZero
    rw [← hEq, abs_of_nonneg hTnonneg]
  have hsummandSupport (sigma : ℝ) :
      (fun u : ℂ => (D u : ℂ) *
        ((((sigma : ℂ) + I * T) - u)⁻¹)).support ⊆ S := by
    intro u hu
    apply hfinite.mem_toFinset.mpr
    by_contra hDu
    have hDuZero : D u = 0 := by
      simpa [Function.mem_support] using hDu
    exact hu (by simp [hDuZero])
  have hprincipal (sigma : ℝ) :
      shiftedDivisorPrincipalPart T sigma =
        ∑ u ∈ S, (D u : ℂ) *
          ((((sigma : ℂ) + I * T) - u)⁻¹) := by
    rw [shiftedDivisorPrincipalPart]
    simpa [D] using
      (finsum_eq_sum_of_support_subset
        (fun u : ℂ => (D u : ℂ) *
          ((((sigma : ℂ) + I * T) - u)⁻¹))
        (hsummandSupport sigma))
  have hne (u : ℂ) (hu : u ∈ S) (sigma : ℝ) :
      ((sigma : ℂ) + I * T) - u ≠ 0 := by
    intro hz
    have him : T - u.im = 0 := by
      simpa using congrArg Complex.im hz
    exact hheight u hu (sub_eq_zero.mp him)
  rw [show (fun sigma : ℝ =>
      (shiftedDivisorPrincipalPart T sigma).im) =
        fun sigma : ℝ => ∑ u ∈ S, (D u : ℝ) *
          (((((sigma : ℂ) + I * T) - u)⁻¹).im) by
      funext sigma
      rw [hprincipal]
      simp]
  apply Continuous.intervalIntegrable (μ := MeasureTheory.volume)
  · exact continuous_finset_sum S (fun u hu => by
      have hinv : Continuous fun sigma : ℝ =>
          ((((sigma : ℂ) + I * T) - u)⁻¹) := by
        exact (by fun_prop : Continuous fun sigma : ℝ =>
          ((sigma : ℂ) + I * T) - u).inv₀ (hne u hu)
      simpa only [Function.comp_apply] using
        (Complex.continuous_im.comp hinv).const_mul (D u : ℝ))

/-- The branch-free zeta argument variation along the upper horizontal segment
from `Re(s)=1/2` to `Re(s)=2`. -/
noncomputable def zetaHorizontalArgumentVariation (T : ℝ) : ℝ :=
  ∫ sigma in (1 / 2 : ℝ)..2,
    (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im

/-- At every sufficiently high good height, the zeta contribution to the
horizontal argument variation is `O(log T)`. -/
theorem exists_abs_zetaHorizontalArgumentVariation_le_log :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ T : ℝ, 4 ≤ T →
      ExplicitFormulaAux.goodHeight T →
      |zetaHorizontalArgumentVariation T| ≤
        C * (1 + Real.log (T + 5)) := by
  rcases ZeroFreeRegion.exists_shifted_disk_regularized_logDeriv_riemannZeta_log_bound with
    ⟨Breg, hBreg, hregular⟩
  rcases ZeroFreeRegion.exists_finsum_divisor_riemannZeta_shifted_disk_log_bound with
    ⟨Bmass, hBmass, hmassBound⟩
  let C : ℝ := (3 / 2 : ℝ) * Breg + Real.pi * Bmass
  have hC : 0 ≤ C := by
    dsimp [C]
    positivity
  refine ⟨C, hC, ?_⟩
  intro T hT hgood
  let L : ℝ := 1 + Real.log (T + 5)
  have hTpos : 0 < T := by linarith
  have hTnonneg : 0 ≤ T := hTpos.le
  have hTabs : 4 ≤ |T| := by simpa [abs_of_nonneg hTnonneg] using hT
  have hL : 0 ≤ L := by
    dsimp [L]
    have hlog : 0 ≤ Real.log (T + 5) :=
      Real.log_nonneg (by linarith)
    linarith
  have hlogInt : IntervalIntegrable
      (fun sigma : ℝ =>
        (logDeriv riemannZeta ((sigma : ℂ) + I * T)).im)
      MeasureTheory.volume (1 / 2 : ℝ) 2 :=
    intervalIntegrable_logDeriv_im_goodHeight_horizontal hTpos hgood
  have hprincipalInt : IntervalIntegrable
      (fun sigma : ℝ => (shiftedDivisorPrincipalPart T sigma).im)
      MeasureTheory.volume (1 / 2 : ℝ) 2 :=
    intervalIntegrable_shiftedDivisorPrincipalPart_im hT hgood
  have hregularInt : IntervalIntegrable
      (fun sigma : ℝ =>
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im)
      MeasureTheory.volume (1 / 2 : ℝ) 2 := by
    simpa only [Complex.sub_im] using hlogInt.sub hprincipalInt
  have hregularIntegral :
      |∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im| ≤
        Breg * L * (3 / 2 : ℝ) := by
    have hbound := intervalIntegral.norm_integral_le_of_norm_le_const
      (f := fun sigma : ℝ =>
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im)
      (a := (1 / 2 : ℝ)) (b := 2) (C := Breg * L)
      (fun sigma hsigma => by
        rw [Set.uIoc_of_le (by norm_num : (1 / 2 : ℝ) ≤ 2)] at hsigma
        let z : ℂ := (sigma : ℂ) + I * T
        let c : ℂ := (3 / 2 : ℂ) + I * T
        have hzball : z ∈ Metric.closedBall c 1 := by
          rw [Metric.mem_closedBall, dist_eq_norm]
          have heq : z - c = ((sigma - 3 / 2 : ℝ) : ℂ) := by
            apply Complex.ext <;> simp [z, c]
          rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_le]
          constructor <;> linarith [hsigma.1.le, hsigma.2]
        have hzeta : riemannZeta z ≠ 0 := by
          exact ExplicitFormulaResidues.riemannZeta_ne_zero_on_goodHeight_horizontal
            (T := T) (t := T) (σ := sigma) hTpos
            (abs_of_pos hTpos) hgood
        have hreg := hregular T hTabs z (by simpa [c] using hzball) hzeta
        have him :
            |(logDeriv riemannZeta z -
              shiftedDivisorPrincipalPart T sigma).im| ≤
              ‖logDeriv riemannZeta z -
                shiftedDivisorPrincipalPart T sigma‖ :=
          Complex.abs_im_le_norm _
        have hreg' :
            ‖logDeriv riemannZeta z -
              shiftedDivisorPrincipalPart T sigma‖ ≤ Breg * L := by
          simpa [shiftedDivisorPrincipalPart, shiftedZetaDivisor, z, c, L,
            abs_of_nonneg hTnonneg]
            using hreg
        simpa [Real.norm_eq_abs, z] using him.trans hreg')
    rw [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2 - 1 / 2)] at hbound
    convert hbound using 1
    ring
  have hmass :
      (∑ᶠ u, (shiftedZetaDivisor T u : ℝ)) ≤ Bmass * L := by
    simpa [shiftedZetaDivisor, L, abs_of_nonneg hTnonneg] using
      hmassBound T hTabs
  have hprincipalIntegral :
      |∫ sigma in (1 / 2 : ℝ)..2,
        (shiftedDivisorPrincipalPart T sigma).im| ≤
        Real.pi * Bmass * L := by
    calc
      |∫ sigma in (1 / 2 : ℝ)..2,
          (shiftedDivisorPrincipalPart T sigma).im| ≤
          Real.pi * ∑ᶠ u, (shiftedZetaDivisor T u : ℝ) :=
        abs_integral_im_shiftedDivisorPrincipalPart_le_pi_mul_mass hT hgood
      _ ≤ Real.pi * (Bmass * L) :=
        mul_le_mul_of_nonneg_left hmass Real.pi_pos.le
      _ = Real.pi * Bmass * L := by ring
  have hsplit : zetaHorizontalArgumentVariation T =
      (∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im) +
      ∫ sigma in (1 / 2 : ℝ)..2,
        (shiftedDivisorPrincipalPart T sigma).im := by
    rw [zetaHorizontalArgumentVariation]
    rw [← intervalIntegral.integral_add hregularInt hprincipalInt]
    congr 1
    funext sigma
    simp
  rw [hsplit]
  calc
    |(∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im) +
        ∫ sigma in (1 / 2 : ℝ)..2,
          (shiftedDivisorPrincipalPart T sigma).im| ≤
      |∫ sigma in (1 / 2 : ℝ)..2,
        (logDeriv riemannZeta ((sigma : ℂ) + I * T) -
          shiftedDivisorPrincipalPart T sigma).im| +
        |∫ sigma in (1 / 2 : ℝ)..2,
          (shiftedDivisorPrincipalPart T sigma).im| := abs_add_le _ _
    _ ≤ Breg * L * (3 / 2 : ℝ) + Real.pi * Bmass * L :=
      add_le_add hregularIntegral hprincipalIntegral
    _ = C * (1 + Real.log (T + 5)) := by
      simp only [C, L]
      ring

end RiemannVonMangoldt
end PrimeNumberTheorem
