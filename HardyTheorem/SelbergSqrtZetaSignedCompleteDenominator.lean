import HardyTheorem.SelbergSqrtZetaSignedCoprimeRayLogExpansion

/-!
# Complete denominator fibers for the signed square-root-zeta model

Inside the common truncation range, every factorization `m * r = k` occurs
in the finite denominator support.  The denominator fiber is therefore the
full Dirichlet-convolution fiber, so its arithmetic sum can be replaced
exactly by convolution with the arithmetic zeta function.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- If `A` is the arithmetic coefficient of `zeta^(-1/2)`, then
`zeta * (A log)` is minus the logarithmic coefficient of `zeta * A`.
This is the global identity behind the cancellation of the two single-log
terms on a complete coprime ray. -/
theorem zeta_mul_selbergSqrtZetaLogCoeff :
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaLogCoeff =
      -(((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaCoeff).pmul ArithmeticFunction.log) := by
  let Z : ArithmeticFunction ℝ :=
    (ArithmeticFunction.zeta : ArithmeticFunction ℝ)
  let A : ArithmeticFunction ℝ := selbergSqrtZetaCoeff
  let L : ArithmeticFunction ℝ := selbergSqrtZetaLogCoeff
  let C : ArithmeticFunction ℝ := Z * A
  have hAC : A * C = 1 := by
    dsimp only [C, Z, A]
    calc
      selbergSqrtZetaCoeff *
          ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) =
          (selbergSqrtZetaCoeff * selbergSqrtZetaCoeff) *
            (ArithmeticFunction.zeta : ArithmeticFunction ℝ) := by ring
      _ = 1 := selbergSqrtZetaCoeff_sq_mul_zeta
  have hCC : C * C = Z := by
    calc
      C * C = Z * ((A * A) * Z) := by
        dsimp only [C]
        ring
      _ = Z * 1 := by
        dsimp only [A, Z]
        rw [selbergSqrtZetaCoeff_sq_mul_zeta]
      _ = Z := mul_one Z
  have honeLog :
      (1 : ArithmeticFunction ℝ).pmul ArithmeticFunction.log = 0 := by
    ext n
    by_cases hn : n = 1
    · subst n
      simp [ArithmeticFunction.pmul_apply]
    · simp [ArithmeticFunction.pmul_apply, hn]
  have hLeib := arithmeticFunction_pmul_log_mul A C
  have hLC :
      L * C = -(A * C.pmul ArithmeticFunction.log) := by
    rw [hAC, honeLog] at hLeib
    change
      0 = L * C + A * C.pmul ArithmeticFunction.log at hLeib
    exact eq_neg_of_add_eq_zero_left hLeib.symm
  change Z * L = -(C.pmul ArithmeticFunction.log)
  calc
    Z * L = (C * C) * L := by rw [hCC]
    _ = C * (L * C) := by ring
    _ = C * (-(A * C.pmul ArithmeticFunction.log)) := by rw [hLC]
    _ = -((C * A) * C.pmul ArithmeticFunction.log) := by ring
    _ = -(C.pmul ArithmeticFunction.log) := by
      rw [mul_comm C A, hAC, one_mul]

/-- In the common truncation range, the finite denominator fiber is the full
divisor antidiagonal. -/
theorem selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal
    {N X k : ℕ} (hk : 0 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaSignedDenominatorFiber N X k =
      k.divisorsAntidiagonal := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpRaw, hprod⟩
    rcases Finset.mem_product.mp hpRaw with ⟨hm, hr⟩
    rcases Finset.mem_Icc.mp hm with ⟨hm1, hmN⟩
    rcases Finset.mem_Icc.mp hr with ⟨hr1, hrX⟩
    exact Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hk.ne'⟩
  · intro hp
    rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hne⟩
    have hprod0 : p.1 * p.2 ≠ 0 := by
      rw [hprod]
      exact hne
    have hm0 : p.1 ≠ 0 := left_ne_zero_of_mul hprod0
    have hr0 : p.2 ≠ 0 := right_ne_zero_of_mul hprod0
    have hmDvd : p.1 ∣ k := ⟨p.2, hprod.symm⟩
    have hrDvd : p.2 ∣ k := ⟨p.1, by simpa [Nat.mul_comm] using hprod.symm⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ?_,
      Finset.mem_Icc.mpr ?_⟩, hprod⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hm0,
        (Nat.le_of_dvd hk hmDvd).trans hkN⟩
    · exact ⟨Nat.one_le_iff_ne_zero.mpr hr0,
        (Nat.le_of_dvd hk hrDvd).trans hkX⟩

/-- A complete denominator fiber is exactly convolution with arithmetic
zeta.  This version is uniform in the coefficient function and is the bridge
used by the four terms of the logarithmic taper expansion. -/
theorem sum_selbergSqrtZetaSignedDenominatorFiber_eq_zeta_mul
    (v : ArithmeticFunction ℝ) {N X k : ℕ}
    (hk : 0 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    (∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k, v p.2) =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * v) k := by
  rw [selbergSqrtZetaSignedDenominatorFiber_eq_divisorsAntidiagonal
    hk hkN hkX, ArithmeticFunction.mul_apply]
  apply Finset.sum_congr rfl
  intro p hp
  rcases Nat.mem_divisorsAntidiagonal.mp hp with ⟨hprod, hne⟩
  have hprod0 : p.1 * p.2 ≠ 0 := by
    rw [hprod]
    exact hne
  rw [ArithmeticFunction.natCoe_apply]
  have hp : p.1 ≠ 0 := by
    intro hp
    apply hprod0
    rw [hp]
    simp
  rw [ArithmeticFunction.zeta_apply_ne hp]
  simp

/-- The complete arithmetic denominator coefficient is the zeta convolution
of the unrestricted tapered coefficient. -/
theorem selbergSqrtZetaSignedDenominatorArithmeticCoeff_eq_zeta_mul
    {N X k : ℕ} (hk : 0 < k) (hkN : k ≤ N) (hkX : k ≤ X) :
    selbergSqrtZetaSignedDenominatorArithmeticCoeff N X k =
      ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
        selbergSqrtZetaFullTapered X) k := by
  calc
    selbergSqrtZetaSignedDenominatorArithmeticCoeff N X k =
        ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
          selbergSqrtZetaFullTapered X p.2 := by
      unfold selbergSqrtZetaSignedDenominatorArithmeticCoeff
      apply Finset.sum_congr rfl
      intro p _hp
      rw [selbergSqrtZetaFullTapered_apply]
      rfl
    _ = ((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaFullTapered X) k :=
      sum_selbergSqrtZetaSignedDenominatorFiber_eq_zeta_mul
        (selbergSqrtZetaFullTapered X) hk hkN hkX

/-- Scales for which the denominator product `b * d` lies in both truncation
ranges.  On this part of a ray, the finite denominator fiber is complete. -/
noncomputable def selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport
    (N X a b : ℕ) : Finset ℕ :=
  (selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b).filter fun d =>
    b * d ≤ N ∧ b * d ≤ X

/-- The complementary scales on a fixed ray.  These are the only scales at
which denominator truncation can obstruct the global convolution identities. -/
noncomputable def selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport
    (N X a b : ℕ) : Finset ℕ :=
  (selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b).filter fun d =>
    ¬ (b * d ≤ N ∧ b * d ≤ X)

/-- Exact complete-range/boundary decomposition of a fixed-ray bilinear sum.
The complete part is rewritten as convolution with arithmetic zeta; every
truncation defect is confined to the explicit boundary support. -/
theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_eq_complete_zeta_add_boundary
    (N X a b : ℕ) (u : ℕ → ℝ) (v : ArithmeticFunction ℝ)
    (hb : 0 < b) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u v =
      (∑ d ∈
          selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
        (d : ℝ)⁻¹ * u (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) * v) (b * d))) +
      ∑ d ∈
          selbergSqrtZetaSignedCoprimeRayBoundaryScaleSupport N X a b,
        (d : ℝ)⁻¹ * u (a * d) *
          ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
            v p.2 := by
  classical
  let S := selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b
  let P : ℕ → Prop := fun d => b * d ≤ N ∧ b * d ≤ X
  let f : ℕ → ℝ := fun d =>
    (d : ℝ)⁻¹ * u (a * d) *
      ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d), v p.2
  have hsplit :
      (∑ d ∈ S, f d) =
        (∑ d ∈ S.filter P, f d) +
          ∑ d ∈ S.filter (fun d => ¬ P d), f d :=
    (Finset.sum_filter_add_sum_filter_not S P f).symm
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  change (∑ d ∈ S, f d) = _
  rw [hsplit]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  have hdS : d ∈ S := (Finset.mem_filter.mp hd).1
  have hdComplete : P d := (Finset.mem_filter.mp hd).2
  have hdPos : 0 < d := by
    exact (Finset.mem_filter.mp hdS).2.1
  have hbdPos : 0 < b * d := Nat.mul_pos hb hdPos
  dsimp only [f]
  rw [sum_selbergSqrtZetaSignedDenominatorFiber_eq_zeta_mul
    v hbdPos hdComplete.1 hdComplete.2]

/-- On the complete part of a positive coprime ray, the two single-log terms
combine exactly into `log(a / b)` times the untapered term.  In particular,
they cancel on the diagonal ray `a = b`; no absolute values are used. -/
theorem selbergSqrtZetaSignedCoprimeRayComplete_singleLog_eq_logRatio
    (N X a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaLogCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (b * d)) +
        selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaLogCoeff) (b * d)))) =
      (Real.log a - Real.log b) *
        ∑ d ∈
          selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a b,
        (d : ℝ)⁻¹ *
          selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (b * d)) := by
  classical
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  have hdScale :
      d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b :=
    (Finset.mem_filter.mp hd).1
  have hdPos : 0 < d := (Finset.mem_filter.mp hdScale).2.1
  have haNe : (a : ℝ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbNe : (b : ℝ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdNe : (d : ℝ) ≠ 0 := by exact_mod_cast hdPos.ne'
  have hlogA :
      Real.log ((a : ℝ) * d) = Real.log a + Real.log d :=
    Real.log_mul haNe hdNe
  have hlogB :
      Real.log ((b : ℝ) * d) = Real.log b + Real.log d :=
    Real.log_mul hbNe hdNe
  have hZL := congrArg
    (fun f : ArithmeticFunction ℝ => f (b * d))
    zeta_mul_selbergSqrtZetaLogCoeff
  simp only [ArithmeticFunction.neg_apply,
    ArithmeticFunction.pmul_apply,
    ArithmeticFunction.log_apply] at hZL
  push_cast at hZL
  have hL :
      selbergSqrtZetaLogCoeff (a * d) =
        selbergSqrtZetaCoeff (a * d) * Real.log (a * d) := by
    simp [selbergSqrtZetaLogCoeff,
      ArithmeticFunction.pmul_apply,
      ArithmeticFunction.log_apply]
  rw [hL]
  change
    (d : ℝ)⁻¹ *
        (selbergSqrtZetaCoeff (a * d) * Real.log (a * d) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaCoeff) (b * d)) +
          selbergSqrtZetaCoeff (a * d) *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaLogCoeff) (b * d))) =
      (Real.log a - Real.log b) *
        ((d : ℝ)⁻¹ *
          selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (b * d)))
  rw [hZL, hlogA, hlogB]
  ring

/-- The two single-log terms cancel identically on every complete positive
diagonal ray. -/
theorem selbergSqrtZetaSignedCoprimeRayComplete_singleLog_diagonal_eq_zero
    (N X a : ℕ) (ha : 0 < a) :
    (∑ d ∈
        selbergSqrtZetaSignedCoprimeRayCompleteScaleSupport N X a a,
      (d : ℝ)⁻¹ *
        (selbergSqrtZetaLogCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaCoeff) (a * d)) +
        selbergSqrtZetaCoeff (a * d) *
          (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
            selbergSqrtZetaLogCoeff) (a * d)))) = 0 := by
  rw [selbergSqrtZetaSignedCoprimeRayComplete_singleLog_eq_logRatio
    N X a a ha ha]
  ring

end HardyTheorem
