import PrimeNumberTheorem.WindowedMellinL2
import PrimeNumberTheorem.WindowedDetectorResponseKernel
import PrimeNumberTheorem.GlobalZeroCount
import ZeroFreeRegion.MeromorphicAux

/-!
# L2 windowed Mellin response identity

The L2 layer's main identity, documented in
`docs/research/2026-08-24-pr474-windowed-detector-single-layer-forcing.md`,
built on the locally available per-zero cubic kernel (round 38) and the
complex-power fundamental theorem (round 35): the windowed response of the
centered second difference equals the sum of per-zero responses plus a
windowed error of size `O(X^(lam (1-1/20)))`, eventually in `X`.

The truncated explicit formula itself (`hexplicit`) remains an explicit
input: its proof is the cubic line's
`exists_cubicZeroKernelSum_chebyshevPsi_bounds`, whose residue-side
content is now available locally; only the contour-remainder bound is
still owned by the cubic line.
-/

namespace PrimeNumberTheorem
namespace WindowedMellinL2

open Complex
open Filter
open MeasureTheory
open scoped BigOperators
open ExplicitFormulaAux

/-- The centered second forward difference of the Chebyshev ψ function at
log-scale `h`, normalized by `h²`. -/
noncomputable def centeredSecondDifferencePsi (x h : ℝ) : ℝ :=
  (PrimeNumberTheorem.chebyshevPsi (x * Real.exp (2 * h)) -
    2 * PrimeNumberTheorem.chebyshevPsi (x * Real.exp h) +
    PrimeNumberTheorem.chebyshevPsi x) / h ^ 2

/-- The windowed Mellin response of the centered second difference at
frequency `γ` over the window `[X, X^lam]`. -/
noncomputable def windowedResponse (X lam h γ : ℝ) : ℂ :=
  ∫ x in X..X ^ lam,
    (centeredSecondDifferencePsi x h : ℂ) * (x : ℂ) ^ (-1 - Complex.I * γ)

/-- The windowed integral of one cubic zero kernel equals the response
coefficient times the complex response factor. -/
theorem windowedIntegral_cubicKernel_eq_response
    {rho : ℂ} {X lam h γ : ℝ} (hX : 0 < X) (hlam : 1 < lam) (hh : 0 < h)
    (hrho : rho ≠ 0) (hz : rho - Complex.I * γ ≠ 0) :
    (∫ x in X..X ^ lam,
      ExplicitFormulaResidues.cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2 *
        (x : ℂ) ^ (-1 - Complex.I * γ)) =
      zeroResponseCoeff rho h * integralFactor rho X lam γ := by
  have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hX lam
  have hmem_pos : ∀ t ∈ Set.uIcc X (X ^ lam), 0 < t := by
    intro t ht
    rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h2, _⟩
    · exact lt_of_lt_of_le hX h1
    · exact lt_of_lt_of_le hXlam0 h2
  have hfactor :
      (∫ x in X..X ^ lam,
        ExplicitFormulaResidues.cubicZeroResidueSecondDifference rho x h / (h : ℂ) ^ 2 *
          (x : ℂ) ^ (-1 - Complex.I * γ)) =
      (∫ x in X..X ^ lam,
        ExplicitFormulaResidues.cubicSimpleZeroKernel rho x *
          ExplicitFormulaResidues.cubicKernelMultiplier rho h *
          (x : ℂ) ^ (-1 - Complex.I * γ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    simp only [ExplicitFormulaResidues.cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
      (hmem_pos x hx) hh hrho]
  have hconst :
      (∫ x in X..X ^ lam,
        ExplicitFormulaResidues.cubicSimpleZeroKernel rho x *
          ExplicitFormulaResidues.cubicKernelMultiplier rho h *
          (x : ℂ) ^ (-1 - Complex.I * γ)) =
      (∫ x in X..X ^ lam,
        -(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
          ExplicitFormulaResidues.cubicKernelMultiplier rho h *
          (x : ℂ) ^ rho * (x : ℂ) ^ (-1 - Complex.I * γ)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    dsimp [ExplicitFormulaResidues.cubicSimpleZeroKernel]
    ring
  rw [hfactor, hconst]
  have hcong : (fun x : ℝ => -(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
        ExplicitFormulaResidues.cubicKernelMultiplier rho h * (x : ℂ) ^ rho *
        (x : ℂ) ^ (-1 - Complex.I * γ)) =
      (fun x : ℝ => (-(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
        ExplicitFormulaResidues.cubicKernelMultiplier rho h) *
        ((x : ℂ) ^ rho * (x : ℂ) ^ (-1 - Complex.I * γ))) := by
    funext x
    ring
  rw [intervalIntegral.integral_congr (fun x hx => congr_fun hcong x)]
  have hpull : (∫ x in X..X ^ lam, (-(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
        ExplicitFormulaResidues.cubicKernelMultiplier rho h) *
      ((x : ℂ) ^ rho * (x : ℂ) ^ (-1 - Complex.I * γ))) =
    (-(analyticOrderNatAt riemannZeta rho : ℂ) / rho *
      ExplicitFormulaResidues.cubicKernelMultiplier rho h) *
      (∫ x in X..X ^ lam, (x : ℂ) ^ rho * (x : ℂ) ^ (-1 - Complex.I * γ)) := by
    exact intervalIntegral.integral_const_mul _ _
  rw [hpull]
  have hpow :
      (∫ x in X..X ^ lam,
        (x : ℂ) ^ rho * (x : ℂ) ^ (-1 - Complex.I * γ)) =
      (∫ x in X..X ^ lam, (x : ℂ) ^ (rho - Complex.I * γ - 1)) := by
    apply intervalIntegral.integral_congr
    intro x hx
    have hxne : (x : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt (hmem_pos x hx)
    simp only [← Complex.cpow_add rho (-1 - Complex.I * γ) hxne]
    congr 1
    ring
  rw [hpow]
  rw [integral_cpow_eq_integralFactor hX hXlam0 hz]
  dsimp [zeroResponseCoeff]

/-- L2 MAIN (input-parametrized, explicit constant): the windowed response
equals the sum of per-zero responses plus a windowed error bounded by
`Ce (20/19) X^(lam (1-1/20))`, eventually in `X`. -/
theorem windowedMellinResponse_eq_sum_add_error
    {lam h γ Ce : ℝ} (truncated : Finset ℂ) (Err : ℝ → ℂ)
    (hlam : 1 < lam) (hh : 0 < h) (hErrCont : Continuous Err)
    (hCe : 0 ≤ Ce)
    (hnonzero : ∀ ρ ∈ truncated, ρ ≠ 0)
    (hz : ∀ ρ ∈ truncated, ρ - Complex.I * γ ≠ 0)
    (hexplicit : ∀ᶠ x in atTop, (centeredSecondDifferencePsi x h : ℂ) =
        (truncated.sum fun ρ =>
          ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
          Err x)
    (hErrBound : ∀ᶠ x in atTop, ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ)) :
    ∀ᶠ X in atTop,
      ‖windowedResponse X lam h γ - (truncated.sum fun ρ =>
        zeroResponseCoeff ρ h * integralFactor ρ X lam γ)‖ ≤
        Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
  have hgood : ∀ᶠ X in atTop,
      (∀ x ∈ Set.uIcc X (X ^ lam),
        (centeredSecondDifferencePsi x h : ℂ) =
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) + Err x) ∧
      (∀ x ∈ Set.uIcc X (X ^ lam), ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ)) ∧
      0 < X ∧ 1 ≤ X ∧ 0 < X ^ lam := by
    have hboth : ∀ᶠ x in (Filter.atTop : Filter ℝ), ((centeredSecondDifferencePsi x h : ℂ) =
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) + Err x) ∧
        ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ) :=
      hexplicit.and hErrBound
    have hset : ({x : ℝ | ((centeredSecondDifferencePsi x h : ℂ) =
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) + Err x) ∧
        ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ)} : Set ℝ) ∈ Filter.atTop := by
      rw [← Filter.eventually_iff]
      exact hboth
    rcases Filter.mem_atTop_sets.mp hset with
      ⟨a, ha⟩
    have hconj : ∀ x, x ∈ Set.Ici a →
        ((centeredSecondDifferencePsi x h : ℂ) =
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) + Err x) ∧
        (‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ)) := by
      intro x hx
      exact ha x hx
    filter_upwards [Filter.eventually_ge_atTop a, Filter.eventually_ge_atTop (1 : ℝ)] with
      X haX hX1
    have hXpos : 0 < X := lt_of_lt_of_le zero_lt_one hX1
    have hXlam0 : 0 < X ^ lam := Real.rpow_pos_of_pos hXpos lam
    have hsub : Set.uIcc X (X ^ lam) ⊆ Set.Ici a := by
      intro x hx
      rcases Set.mem_uIcc.mp hx with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact h1.trans' haX
      · have hXle : X ≤ X ^ lam := by
          have h1 : X ^ (1 : ℝ) ≤ X ^ lam :=
            Real.rpow_le_rpow_of_exponent_le hX1 hlam.le
          simpa [Real.rpow_one] using h1
        exact h2.trans' (haX.trans hXle)
    exact ⟨(fun x hx => (hconj x (hsub hx)).1),
      (fun x hx => (hconj x (hsub hx)).2), hXpos, hX1, hXlam0⟩
  have hmain {X : ℝ}
      (hXg : (∀ x ∈ Set.uIcc X (X ^ lam),
        (centeredSecondDifferencePsi x h : ℂ) =
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) + Err x) ∧
      (∀ x ∈ Set.uIcc X (X ^ lam), ‖Err x‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ)) ∧
      0 < X ∧ 1 ≤ X ∧ 0 < X ^ lam) :
      ‖windowedResponse X lam h γ - (truncated.sum fun ρ =>
        zeroResponseCoeff ρ h * integralFactor ρ X lam γ)‖ ≤
        (Ce * (20 / 19 : ℝ)) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
    have hXpos : 0 < X := hXg.2.2.1
    have hX1 : 1 ≤ X := hXg.2.2.2.1
    have hXlam0 : 0 < X ^ lam := hXg.2.2.2.2
    have hXle : X ≤ X ^ lam := by
      have h1 : X ^ (1 : ℝ) ≤ X ^ lam :=
        Real.rpow_le_rpow_of_exponent_le hX1 hlam.le
      simpa [Real.rpow_one] using h1
    have hmem_pos : ∀ t ∈ Set.uIcc X (X ^ lam), 0 < t := by
      intro t ht
      rcases Set.mem_uIcc.mp ht with ⟨h1, _⟩ | ⟨h2, _⟩
      · exact lt_of_lt_of_le hXpos h1
      · exact lt_of_lt_of_le hXlam0 h2
    have hident : windowedResponse X lam h γ =
        (∫ x in X..X ^ lam,
          ((truncated.sum fun ρ =>
              ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
            Err x) * (x : ℂ) ^ (-1 - Complex.I * γ)) := by
      dsimp [windowedResponse]
      apply intervalIntegral.integral_congr
      intro x hx
      simp only [hXg.1 x hx]
    have hphase : ContinuousOn (fun x : ℝ => (x : ℂ) ^ (-1 - Complex.I * γ))
        (Set.uIcc X (X ^ lam)) := by
      exact ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
        (fun t ht => (Complex.ofReal_mem_slitPlane).mpr (hmem_pos t ht))
    have hkernel {ρ : ℂ} (hρ : ρ ∈ truncated) :
        ContinuousOn (fun x : ℝ =>
          ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
            (x : ℂ) ^ (-1 - Complex.I * γ)) (Set.uIcc X (X ^ lam)) := by
      have hfact : ∀ x ∈ Set.uIcc X (X ^ lam),
          ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 =
            ExplicitFormulaResidues.cubicSimpleZeroKernel ρ x *
              ExplicitFormulaResidues.cubicKernelMultiplier ρ h := by
        intro x hx
        exact ExplicitFormulaResidues.cubicZeroResidueSecondDifference_div_sq_eq_simple_mul_multiplier
          (hmem_pos x hx) hh (hnonzero ρ hρ)
      have hsimple : ContinuousOn (fun x : ℝ => ExplicitFormulaResidues.cubicSimpleZeroKernel ρ x)
          (Set.uIcc X (X ^ lam)) := by
        dsimp [ExplicitFormulaResidues.cubicSimpleZeroKernel]
        exact ContinuousOn.div_const
          (continuousOn_const.mul
            (ContinuousOn.cpow_const Complex.continuous_ofReal.continuousOn
              (fun t ht => (Complex.ofReal_mem_slitPlane).mpr (hmem_pos t ht)))) ρ
      have hk : ContinuousOn (fun x : ℝ =>
          ExplicitFormulaResidues.cubicSimpleZeroKernel ρ x *
            ExplicitFormulaResidues.cubicKernelMultiplier ρ h *
            (x : ℂ) ^ (-1 - Complex.I * γ)) (Set.uIcc X (X ^ lam)) :=
        (hsimple.mul continuousOn_const).mul hphase
      exact hk.congr_mono (fun x hx => by rw [hfact x hx]) subset_rfl
    have herrcont : ContinuousOn (fun x : ℝ => Err x * (x : ℂ) ^ (-1 - Complex.I * γ))
        (Set.uIcc X (X ^ lam)) :=
      hErrCont.continuousOn.mul hphase
    have hsplit :
        (∫ x in X..X ^ lam,
          ((truncated.sum fun ρ =>
              ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
            Err x) * (x : ℂ) ^ (-1 - Complex.I * γ)) =
        (truncated.sum fun ρ =>
          ∫ x in X..X ^ lam,
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
              (x : ℂ) ^ (-1 - Complex.I * γ)) +
          ∫ x in X..X ^ lam, Err x * (x : ℂ) ^ (-1 - Complex.I * γ) := by
      have hdist : ∀ x ∈ Set.uIcc X (X ^ lam),
          ((truncated.sum fun ρ =>
              ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2) +
            Err x) * (x : ℂ) ^ (-1 - Complex.I * γ) =
          (truncated.sum fun ρ =>
              ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
                (x : ℂ) ^ (-1 - Complex.I * γ)) +
            Err x * (x : ℂ) ^ (-1 - Complex.I * γ) := by
        intro x hx
        simp only [add_mul, Finset.sum_mul]
      rw [intervalIntegral.integral_congr hdist]
      have hsumcont : ContinuousOn (fun x : ℝ =>
          (truncated.sum fun ρ =>
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
              (x : ℂ) ^ (-1 - Complex.I * γ))) (Set.uIcc X (X ^ lam)) := by
        have hmain : ∀ s ⊆ truncated, ContinuousOn (fun x : ℝ =>
            (s.sum fun ρ =>
              ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
                (x : ℂ) ^ (-1 - Complex.I * γ))) (Set.uIcc X (X ^ lam)) := by
          intro s hs
          induction s using Finset.induction with
          | empty =>
              intro x hx
              simpa [Finset.sum_empty] using (continuousWithinAt_const :
                ContinuousWithinAt (fun _ : ℝ => (0 : ℂ)) (Set.uIcc X (X ^ lam)) x)
          | insert ρ s hρs ih =>
              intro x hx
              have hρt : ρ ∈ truncated := hs (Finset.mem_insert_self ρ s)
              have hst : s ⊆ truncated := fun a ha => hs (Finset.mem_insert_of_mem ha)
              have h1 := ih hst x hx
              have h2 := hkernel hρt x hx
              simp only [Finset.sum_insert hρs]
              exact h2.add h1
        exact hmain truncated subset_rfl
      rw [intervalIntegral.integral_add hsumcont.intervalIntegrable herrcont.intervalIntegrable]
      rw [intervalIntegral.integral_finset_sum (fun ρ hρ => (hkernel hρ).intervalIntegrable)]
    have hkernels :
        (truncated.sum fun ρ =>
          ∫ x in X..X ^ lam,
            ExplicitFormulaResidues.cubicZeroResidueSecondDifference ρ x h / (h : ℂ) ^ 2 *
              (x : ℂ) ^ (-1 - Complex.I * γ)) =
        truncated.sum fun ρ =>
          zeroResponseCoeff ρ h * integralFactor ρ X lam γ := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      exact windowedIntegral_cubicKernel_eq_response hXpos hlam hh
        (hnonzero ρ hρ) (hz ρ hρ)
    have herrbound :
        ‖∫ x in X..X ^ lam, Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖ ≤
          Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
      have h1 := intervalIntegral.norm_integral_le_integral_norm
        (f := fun x : ℝ => Err x * (x : ℂ) ^ (-1 - Complex.I * γ)) (a := X) (b := X ^ lam)
        (μ := volume) hXle
      have hle : ∀ x ∈ Set.uIcc X (X ^ lam),
          ‖Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖ ≤ Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ) := by
        intro x hx
        have hposx : 0 < x := hmem_pos x hx
        rw [norm_mul]
        rw [norm_cpow_ofReal_pos (t := x) (z := -1 - Complex.I * γ) hposx]
        have hzre : (-1 - Complex.I * γ).re = -1 := by
          simp [Complex.sub_re, Complex.mul_re, Complex.mul_im]
        rw [hzre]
        exact mul_le_mul_of_nonneg_right (hXg.2.1 x hx)
          (by positivity : 0 ≤ x ^ (-1 : ℝ))
      have hfcont : ContinuousOn (fun x : ℝ => ‖Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖)
          (Set.uIcc X (X ^ lam)) :=
        herrcont.norm
      have hfint : IntervalIntegrable (fun x : ℝ => ‖Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖)
          volume X (X ^ lam) :=
        hfcont.intervalIntegrable
      have hgcont : ContinuousOn (fun x : ℝ => Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ))
          (Set.uIcc X (X ^ lam)) := by
        intro x hx
        have h1 : ContinuousWithinAt (fun t : ℝ => Ce * t ^ (1 - 1 / 20 : ℝ))
            (Set.uIcc X (X ^ lam)) x := by
          exact (ContinuousAt.continuousWithinAt
            (continuousAt_const.mul
              (Real.continuousAt_rpow_const x (1 - 1 / 20 : ℝ) (Or.inl (ne_of_gt (hmem_pos x hx))))))
        have h2 : ContinuousWithinAt (fun t : ℝ => t ^ (-1 : ℝ))
            (Set.uIcc X (X ^ lam)) x := by
          exact (ContinuousAt.continuousWithinAt
            (Real.continuousAt_rpow_const x (-1 : ℝ) (Or.inl (ne_of_gt (hmem_pos x hx)))))
        exact h1.mul h2
      have hgint : IntervalIntegrable (fun x : ℝ => Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ))
          volume X (X ^ lam) :=
        hgcont.intervalIntegrable
      have h2 := intervalIntegral.integral_mono_on
        (f := fun x : ℝ => ‖Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖)
        (g := fun x : ℝ => Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ))
        (a := X) (b := X ^ lam) (μ := volume)
        hXle hfint hgint
        (fun x hx => hle x (Set.mem_uIcc.mpr (Or.inl hx)))
      have h3 : (∫ x in X..X ^ lam, Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ)) =
          Ce * (∫ x in X..X ^ lam, x ^ ((-1 : ℝ) / 20)) := by
        have hcong : (∫ x in X..X ^ lam, Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ)) =
            (∫ x in X..X ^ lam, Ce * x ^ ((-1 : ℝ) / 20)) := by
          apply intervalIntegral.integral_congr
          intro x hx
          simp only [mul_assoc]
          rw [← Real.rpow_add (hmem_pos x hx) (1 - 1 / 20 : ℝ) (-1 : ℝ)]
          congr 1
          ring
        rw [hcong]
        exact intervalIntegral.integral_const_mul Ce (fun x : ℝ => x ^ ((-1 : ℝ) / 20))
      have h4 : (∫ x in X..X ^ lam, x ^ ((-1 : ℝ) / 20)) =
          (20 / 19 : ℝ) * (X ^ (lam * (1 - 1 / 20 : ℝ)) - X ^ (1 - 1 / 20 : ℝ)) := by
        have hcong : (fun x : ℝ => x ^ ((-1 : ℝ) / 20)) =
            (fun x : ℝ => x ^ ((1 - 1 / 20 : ℝ) - 1)) := by
          funext x
          congr 1
          norm_num
        rw [intervalIntegral.integral_congr (fun x hx => congr_fun hcong x)]
        have hβ := integral_rpow_sub_one_eq (X := X) (lam := lam) (β := (1 - 1 / 20 : ℝ))
          hXpos hXlam0 (by norm_num : (1 - 1 / 20 : ℝ) ≠ 0)
        have hp : (X ^ lam) ^ (1 - 1 / 20 : ℝ) = X ^ (lam * (1 - 1 / 20 : ℝ)) := by
          rw [Real.rpow_mul hXpos.le lam (1 - 1 / 20 : ℝ)]
        rw [hβ]
        rw [hp]
        field_simp [(by norm_num : (1 - 1 / 20 : ℝ) ≠ 0)]
        ring
      calc
        ‖∫ x in X..X ^ lam, Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖ ≤
            ∫ x in X..X ^ lam, ‖Err x * (x : ℂ) ^ (-1 - Complex.I * γ)‖ := h1
        _ ≤ ∫ x in X..X ^ lam, Ce * x ^ (1 - 1 / 20 : ℝ) * x ^ (-1 : ℝ) := h2
        _ = Ce * ((20 / 19 : ℝ) * (X ^ (lam * (1 - 1 / 20 : ℝ)) - X ^ (1 - 1 / 20 : ℝ))) := by
          rw [h3, h4]
        _ ≤ Ce * (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
          have hsub : (20 / 19 : ℝ) * (X ^ (lam * (1 - 1 / 20 : ℝ)) - X ^ (1 - 1 / 20 : ℝ)) ≤
              (20 / 19 : ℝ) * X ^ (lam * (1 - 1 / 20 : ℝ)) := by
            exact mul_le_mul_of_nonneg_left
              (sub_le_self _ (Real.rpow_nonneg hXpos.le (1 - 1 / 20 : ℝ)))
              (by norm_num : 0 ≤ (20 / 19 : ℝ))
          simpa [mul_assoc] using mul_le_mul_of_nonneg_left hsub hCe
    have hmain' : windowedResponse X lam h γ - (truncated.sum fun ρ =>
        zeroResponseCoeff ρ h * integralFactor ρ X lam γ) =
      ∫ x in X..X ^ lam, Err x * (x : ℂ) ^ (-1 - Complex.I * γ) := by
      rw [hident]
      rw [hsplit]
      rw [hkernels]
      abel
    rw [hmain']
    exact herrbound
  filter_upwards [hgood] with X hXg
  exact hmain hXg

end WindowedMellinL2
end PrimeNumberTheorem
