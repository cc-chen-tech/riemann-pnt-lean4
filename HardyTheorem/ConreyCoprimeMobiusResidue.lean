import ZeroFreeRegion.MeromorphicAux
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv

open Complex MeasureTheory Metric Filter Set
open scoped BigOperators Topology

namespace HardyTheorem

/-!
# The actual regularized coprime Möbius reciprocal and its Perron residue

The pole unit of zeta constructs a holomorphic reciprocal with its correct
value at the pole. A single disk and quadratic error constant work for every
coprimality modulus. The final circle integral is the actual Euler integrand,
not a supplied analytic surrogate. No contour error or inner asymptotic is assumed.
-/

noncomputable def conreyCoprimeEulerInverse (d : ℕ) (z : ℂ) : ℂ :=
  (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹

noncomputable def conreyMobiusPoleUnit (z : ℂ) : ℂ :=
  (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z))⁻¹

noncomputable def conreyCoprimeMobiusRegularized (d : ℕ) (z : ℂ) : ℂ :=
  z * conreyMobiusPoleUnit z * conreyCoprimeEulerInverse d z

private theorem analyticAt_conreyCoprimeEulerInverse (d : ℕ) {z : ℂ}
    (hz : -1 < z.re) : AnalyticAt ℂ (conreyCoprimeEulerInverse d) z := by
  have hF : Differentiable ℂ (fun w : ℂ =>
      ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + w)))) := by
    apply Differentiable.fun_finsetProd
    intro p hp
    exact (differentiable_const (1 : ℂ)).sub
      (((differentiable_const (1 : ℂ)).add differentiable_id).neg.const_cpow
        (Or.inl (Nat.cast_ne_zero.mpr (Nat.prime_of_mem_primeFactors hp).ne_zero)))
  have hFne : (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z)))) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hn : ‖(p : ℂ) ^ (-(1 + z))‖ < 1 := by
      rw [show (p : ℂ) = ((p : ℝ) : ℂ) by simp,
        Complex.norm_cpow_eq_rpow_re_of_pos hp0]
      apply Real.rpow_lt_one_of_one_lt_of_neg hp1
      simp only [neg_re, add_re, one_re]
      linarith
    exact sub_ne_zero.mpr (fun h => by rw [← h, norm_one] at hn; linarith)
  exact (hF.analyticAt z).inv hFne

@[simp] theorem conreyMobiusPoleUnit_zero : conreyMobiusPoleUnit 0 = 1 := by
  simp [conreyMobiusPoleUnit, ZeroFreeRegion.riemannZetaPoleUnitAtOne_one]

private theorem analyticAt_conreyMobiusPoleUnit_zero :
    AnalyticAt ℂ conreyMobiusPoleUnit 0 := by
  have hQ : AnalyticAt ℂ ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + (0 : ℂ)) := by
    simpa using ZeroFreeRegion.analyticAt_riemannZetaPoleUnitAtOne
  exact (hQ.comp (analyticAt_const.add analyticAt_id)).inv
    (by simp [ZeroFreeRegion.riemannZetaPoleUnitAtOne_one])

private theorem exists_conreyMobiusPoleUnit_disk :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 < C ∧ ∀ z : ℂ, ‖z‖ ≤ r →
      AnalyticAt ℂ conreyMobiusPoleUnit z ∧
        ‖conreyMobiusPoleUnit z - 1‖ ≤ C * ‖z‖ := by
  have ha := analyticAt_conreyMobiusPoleUnit_zero
  obtain ⟨C, hC, hbound⟩ := ha.differentiableAt.hasDerivAt.isBigO_sub.exists_pos
  have hevent : ∀ᶠ z in 𝓝 (0 : ℂ),
      AnalyticAt ℂ conreyMobiusPoleUnit z ∧
        ‖conreyMobiusPoleUnit z - 1‖ ≤ C * ‖z‖ := by
    exact ha.eventually_analyticAt.and (by simpa using hbound.bound)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hevent
  let r : ℝ := min (δ / 2) (1 / 4)
  have hr : 0 < r := lt_min (by linarith) (by norm_num)
  refine ⟨r, C, hr, min_le_right _ _, hC, ?_⟩
  intro z hz
  apply hball
  rw [mem_ball_zero_iff]
  exact lt_of_le_of_lt (hz.trans (min_le_left _ _)) (by linarith)

/-- Away from the removable point, the regularization is the literal Euler reciprocal. -/
theorem conreyCoprimeMobiusRegularized_eq_euler (d : ℕ) {z : ℂ}
    (hz : z ≠ 0) (hz1 : 1 + z ≠ 0) :
    conreyCoprimeMobiusRegularized d z =
      (riemannZeta (1 + z) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹ := by
  have hnot1 : 1 + z ≠ 1 := by simpa using hz
  unfold conreyCoprimeMobiusRegularized conreyMobiusPoleUnit conreyCoprimeEulerInverse
  rw [ZeroFreeRegion.riemannZetaPoleUnitAtOne_eq_sub_one_mul_riemannZeta hz1 hnot1]
  simp only [add_sub_cancel_left, mul_inv_rev]
  calc
    _ = (z * z⁻¹) * ((riemannZeta (1 + z))⁻¹ *
        (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹) := by ring
    _ = _ := by rw [mul_inv_cancel₀ hz]; ring

private theorem conreyCoprimeMobiusRegularized_circle
    (d : ℕ) {r : ℝ} (hr : r ≤ 1 / 4)
    (hW : AnalyticOnNhd ℂ (conreyCoprimeMobiusRegularized d) (closedBall 0 r))
    (α : ℂ) {X ρ : ℝ} (hX : 0 < X) (hαρ : ‖α‖ < ρ) (hρr : ‖α‖ + ρ ≤ r) :
    CircleIntegrable (fun w : ℂ => (X : ℂ) ^ w *
      (riemannZeta (1 + α + w) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
      (1 / w ^ 2)) 0 ρ ∧
    (∮ w in C(0, ρ), (X : ℂ) ^ w *
      (riemannZeta (1 + α + w) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
      (1 / w ^ 2)) = (2 * Real.pi * I) *
      ((Real.log X : ℂ) * conreyCoprimeMobiusRegularized d α +
        deriv (conreyCoprimeMobiusRegularized d) α) := by
  have hρ : 0 < ρ := (norm_nonneg α).trans_lt hαρ
  have hshift {w : ℂ} (hw : ‖w‖ ≤ ρ) : ‖α + w‖ ≤ r :=
    (norm_add_le α w).trans ((add_le_add le_rfl hw).trans hρr)
  have hαr : ‖α‖ ≤ r := by linarith
  have hX0 : (X : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hX.ne'
  let f : ℂ → ℂ := fun w => (X : ℂ) ^ w * conreyCoprimeMobiusRegularized d (α + w)
  have hf : AnalyticOnNhd ℂ f (closedBall 0 ρ) := by
    intro w hw
    have hw' : ‖w‖ ≤ ρ := by simpa using hw
    exact ((differentiable_id.const_cpow (Or.inl hX0)).analyticAt w).mul
      ((hW (α + w) (by simpa using hshift hw')).comp (analyticAt_const.add analyticAt_id))
  have hboundary : EqOn (fun w : ℂ => (X : ℂ) ^ w *
      (riemannZeta (1 + α + w) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
      (1 / w ^ 2)) (fun w => (1 / (w - 0) ^ 2) • f w) (sphere 0 ρ) := by
    intro w hw
    have hwn : ‖w‖ = ρ := by simpa using hw
    have hz : α + w ≠ 0 := by
      intro hz
      have heq : α = -w := eq_neg_of_add_eq_zero_left hz
      have hn : ‖α‖ = ρ := by rw [heq, norm_neg, hwn]
      linarith
    have hz1 : 1 + (α + w) ≠ 0 := by
      apply Complex.ne_zero_of_re_pos
      have hlo := (abs_le.mp (Complex.abs_re_le_norm (α + w))).1
      have hnorm := hshift hwn.le
      simp only [add_re] at hlo
      simp only [add_re, one_re]
      linarith
    have heq := conreyCoprimeMobiusRegularized_eq_euler d hz hz1
    simp only [f, heq, sub_zero, smul_eq_mul, ← add_assoc]
    ring
  have hk : ContinuousOn (fun w : ℂ => (1 / (w - 0) ^ 2) • f w) (sphere 0 ρ) := by
    apply ContinuousOn.fun_smul
    · apply continuousOn_const.div (continuousOn_id.sub continuousOn_const |>.pow 2)
      intro w hw
      apply pow_ne_zero
      have hn : ‖w‖ = ρ := by simpa using hw
      simpa using (norm_pos_iff.mp (by linarith : 0 < ‖w‖))
    · exact hf.continuousOn.mono sphere_subset_closedBall
  have hderiv : deriv f 0 =
      (Real.log X : ℂ) * conreyCoprimeMobiusRegularized d α +
        deriv (conreyCoprimeMobiusRegularized d) α := by
    have hx : HasDerivAt (fun w : ℂ => (X : ℂ) ^ w) (Complex.log (X : ℂ)) 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_cpow (Or.inl hX0)
    have hw : HasDerivAt (fun w : ℂ => conreyCoprimeMobiusRegularized d (α + w))
        (deriv (conreyCoprimeMobiusRegularized d) α) 0 := by
      apply HasDerivAt.comp_const_add
      simpa using (hW α (by simpa using hαr)).differentiableAt.hasDerivAt
    simpa [f, ← Complex.ofReal_log hX.le] using (hx.fun_mul hw).deriv
  refine ⟨(hk.congr hboundary).circleIntegrable hρ.le, ?_⟩
  rw [circleIntegral.integral_congr hρ.le hboundary]
  have hc := hf.differentiableOn.deriv_eq_smul_circleIntegral hρ
  simpa only [smul_eq_mul, hderiv] using hc

/-- An unconditional common disk, genuine removable value and derivative,
quadratic local error, and exact circle residue for the actual Perron integrand. -/
theorem exists_conrey_coprime_mobius_local_residue :
    ∃ r C : ℝ, 0 < r ∧ r ≤ 1 / 4 ∧ 0 < C ∧ ∀ d : ℕ,
      let E : ℂ → ℂ := fun z =>
        (∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹
      let W : ℂ → ℂ := fun z =>
        z * (ZeroFreeRegion.riemannZetaPoleUnitAtOne (1 + z))⁻¹ * E z
      AnalyticOnNhd ℂ W (closedBall 0 r) ∧ W 0 = 0 ∧ deriv W 0 = E 0 ∧
      (∀ z : ℂ, ‖z‖ ≤ r → ‖W z - z * E z‖ ≤ C * ‖z‖ ^ 2 * ‖E z‖) ∧
      (∀ z : ℂ, ‖z‖ ≤ r → z ≠ 0 →
        W z = (riemannZeta (1 + z) *
          ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + z))))⁻¹) ∧
      ∀ (α : ℂ) (X ρ : ℝ), 0 < X → ‖α‖ < ρ → ‖α‖ + ρ ≤ r →
        CircleIntegrable (fun w : ℂ => (X : ℂ) ^ w *
          (riemannZeta (1 + α + w) *
            ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
          (1 / w ^ 2)) 0 ρ ∧
        (∮ w in C(0, ρ), (X : ℂ) ^ w *
          (riemannZeta (1 + α + w) *
            ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + w))))⁻¹ *
          (1 / w ^ 2)) =
        (2 * Real.pi * I) * ((Real.log X : ℂ) * W α + deriv W α) := by
  obtain ⟨r, C, hr, hr4, hC, hU⟩ := exists_conreyMobiusPoleUnit_disk
  refine ⟨r, C, hr, hr4, hC, ?_⟩
  intro d
  change AnalyticOnNhd ℂ (conreyCoprimeMobiusRegularized d) (closedBall 0 r) ∧ _
  have hre {z : ℂ} (hz : ‖z‖ ≤ r) : -1 < z.re := by
    have hlo := (abs_le.mp (Complex.abs_re_le_norm z)).1
    linarith
  have hW : AnalyticOnNhd ℂ (conreyCoprimeMobiusRegularized d) (closedBall 0 r) := by
    intro z hz
    have hn : ‖z‖ ≤ r := by simpa using hz
    exact (analyticAt_id.mul (hU z hn).1).mul (analyticAt_conreyCoprimeEulerInverse d (hre hn))
  refine ⟨hW, ?_, ?_, ?_, ?_, ?_⟩
  · simp
  · change deriv (conreyCoprimeMobiusRegularized d) 0 = conreyCoprimeEulerInverse d 0
    have hu := analyticAt_conreyMobiusPoleUnit_zero.differentiableAt.hasDerivAt
    have he := (analyticAt_conreyCoprimeEulerInverse d (z := 0) (by norm_num)).differentiableAt.hasDerivAt
    have hd := (((hasDerivAt_id (0 : ℂ)).fun_mul hu).fun_mul he).deriv
    change deriv (conreyCoprimeMobiusRegularized d) 0 = _ at hd
    simpa only [id_eq, conreyMobiusPoleUnit_zero, one_mul, zero_mul, add_zero] using hd
  · intro z hz
    change ‖conreyCoprimeMobiusRegularized d z - z * conreyCoprimeEulerInverse d z‖ ≤
      C * ‖z‖ ^ 2 * ‖conreyCoprimeEulerInverse d z‖
    calc
      _ = ‖z‖ * ‖conreyMobiusPoleUnit z - 1‖ * ‖conreyCoprimeEulerInverse d z‖ := by
        rw [show conreyCoprimeMobiusRegularized d z - z * conreyCoprimeEulerInverse d z =
          z * (conreyMobiusPoleUnit z - 1) * conreyCoprimeEulerInverse d z by
            unfold conreyCoprimeMobiusRegularized; ring, norm_mul, norm_mul]
      _ ≤ ‖z‖ * (C * ‖z‖) * ‖conreyCoprimeEulerInverse d z‖ := by
        gcongr
        exact (hU z hz).2
      _ = _ := by ring
  · intro z hz hne
    exact conreyCoprimeMobiusRegularized_eq_euler d hne
      (Complex.ne_zero_of_re_pos (by simp only [add_re, one_re]; linarith [hre hz]))
  · intro α X ρ hX hαρ hρr
    exact conreyCoprimeMobiusRegularized_circle d hr4 hW α hX hαρ hρr

end HardyTheorem
