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

end RiemannVonMangoldt
end PrimeNumberTheorem
