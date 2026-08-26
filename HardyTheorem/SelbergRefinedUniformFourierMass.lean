import HardyTheorem.SelbergUniformWindowFourierMass

open Complex MeasureTheory Set

namespace HardyTheorem

set_option maxHeartbeats 800000

/-!
# Refined full Fourier mass, uniform in the window exponent

The residue and nonconstant pieces must remain separate in the final Selberg
argument.  The residue has its true `X^4` size and is eventually lower order;
the nonconstant term has a constant uniform for `0 < a ≤ 1`, which permits
choosing `a` only after that constant is known.
-/

/-- Low full-kernel mass with the residue retained at its actual `X^4` size
and a nonconstant coefficient uniform for every `0 < a ≤ 1`. -/
theorem exists_integral_normSq_selbergExplicitInverseFourierKernel_low_le_refined_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
            (selbergExplicitInverseFourierKernel delta X y)) ≤
          2 * (X : ℝ) ^ 4 +
            2 * C * (delta ^ (-(1 / 2 : ℝ)) *
              Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
  obtain ⟨C, hC, hN⟩ :=
    exists_integral_normSq_selbergNonconstantInverseFourierKernel_low_le_uniform_unit_window
  refine ⟨C, hC, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hdeltaPi hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let S : ℝ := delta ^ (-(1 / 2 : ℝ)) * Real.log G / Real.log (X : ℝ)
  have hGone : 1 < G := by
    have hG0 : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
    exact (Real.log_pos_iff hG0).mp (by dsimp [G]; linarith)
  have hRint := integrableOn_normSq_selbergResidue_low
    hdelta hdeltaPi X (L := Real.log G)
  have hNint := integrableOn_normSq_selbergNonconstant_low
    hdelta hdeltaOne hdeltaPi hGone hX
  have hmajor : IntegrableOn (fun y =>
      2 * Complex.normSq (selbergResidueInverseFourierKernel delta X y) +
      2 * Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y))
      (Ioc 0 (Real.log G)) :=
    (hRint.const_mul 2).add (hNint.const_mul 2)
  have hR : (∫ y in Ioc 0 (Real.log G),
      Complex.normSq (selbergResidueInverseFourierKernel delta X y)) ≤
      (X : ℝ) ^ 4 :=
    integral_normSq_selbergResidueInverseFourierKernel_low_le_fourth
      hdelta hdeltaPi hX
  have hNb : (∫ y in Ioc 0 (Real.log G),
      Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y)) ≤ C * S := by
    simpa only [G, S] using hN a ha haOne X delta hdelta hdeltaOne hX
      hdeltaPi hXexp hXpow hlogGtwo
  calc
    (∫ y in Ioc 0 (Real.log ((X : ℝ) ^ a)),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y)) ≤
      ∫ y in Ioc 0 (Real.log G),
        (2 * Complex.normSq
          (selbergResidueInverseFourierKernel delta X y) +
         2 * Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with y
          exact Complex.normSq_nonneg _
        · exact hmajor
        · filter_upwards with y
          exact normSq_selbergExplicitInverseFourierKernel_le delta X y
    _ = 2 * (∫ y in Ioc 0 (Real.log G),
          Complex.normSq (selbergResidueInverseFourierKernel delta X y)) +
        2 * (∫ y in Ioc 0 (Real.log G),
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y)) := by
      rw [integral_add (hRint.const_mul 2) (hNint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * (X : ℝ) ^ 4 + 2 * (C * S) := by
      gcongr
    _ = 2 * (X : ℝ) ^ 4 +
        2 * C * (delta ^ (-(1 / 2 : ℝ)) *
          Real.log ((X : ℝ) ^ a) / Real.log (X : ℝ)) := by
      dsimp [S, G]
      ring

/-- High full-kernel mass with the residue retained at `X^4/L^2` and a
nonconstant coefficient uniform for every `0 < a ≤ 1`. -/
theorem exists_integral_normSq_selbergExplicitInverseFourierKernel_high_le_refined_uniform :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (a : ℝ), 0 < a → a ≤ 1 →
      ∀ (X : ℕ) (delta : ℝ),
        0 < delta → delta ≤ 1 → 2 ≤ X → delta < Real.pi / 2 →
        Real.exp 1 ≤ (X : ℝ) →
        (X : ℝ) ≤ delta ^ (-(1 / 32 : ℝ)) →
        2 ≤ Real.log ((X : ℝ) ^ a) →
        (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
          Complex.normSq
              (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
          2 * (X : ℝ) ^ 4 / Real.log ((X : ℝ) ^ a) ^ 2 +
            2 * C * (delta ^ (-(1 / 2 : ℝ)) /
              (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
  obtain ⟨C, hC, hN⟩ :=
    exists_integral_normSq_selbergNonconstantInverseFourierKernel_high_le_uniform_unit_window
  refine ⟨C, hC, ?_⟩
  intro a ha haOne X delta hdelta hdeltaOne hX hdeltaPi hXexp hXpow hlogGtwo
  let G : ℝ := (X : ℝ) ^ a
  let L : ℝ := Real.log G
  let S : ℝ := delta ^ (-(1 / 2 : ℝ)) /
    (L * Real.log (X : ℝ))
  have hGone : 1 < G := by
    have hG0 : 0 ≤ G := Real.rpow_nonneg (Nat.cast_nonneg X) a
    exact (Real.log_pos_iff hG0).mp (by dsimp [G]; linarith)
  have hL : 0 < L := by dsimp [L]; exact Real.log_pos hGone
  have hRint := integrableOn_normSq_selbergResidue_div_sq_high
    hdelta hdeltaPi hL X
  have hNint := integrableOn_normSq_selbergNonconstant_div_sq_high
    hdelta hdeltaOne hdeltaPi hGone hX
  have hmajor : IntegrableOn (fun y =>
      2 * (Complex.normSq
        (selbergResidueInverseFourierKernel delta X y) / y ^ 2) +
      2 * (Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2))
      (Ioi L) := (hRint.const_mul 2).add (hNint.const_mul 2)
  have hR : (∫ y in Ioi L,
      Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
        y ^ 2) ≤ (X : ℝ) ^ 4 / L ^ 2 :=
    integral_normSq_selbergResidueInverseFourierKernel_div_sq_high_le_fourth
      hdelta hdeltaPi hX hL
  have hNb : (∫ y in Ioi L,
      Complex.normSq
        (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2) ≤
      C * S := by
    simpa only [G, L, S] using hN a ha haOne X delta hdelta hdeltaOne hX
      hdeltaPi hXexp hXpow hlogGtwo
  calc
    (∫ y in Ioi (Real.log ((X : ℝ) ^ a)),
        Complex.normSq
          (selbergExplicitInverseFourierKernel delta X y) / y ^ 2) ≤
      ∫ y in Ioi L,
        (2 * (Complex.normSq
          (selbergResidueInverseFourierKernel delta X y) / y ^ 2) +
         2 * (Complex.normSq
          (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2)) := by
        apply integral_mono_of_nonneg
        · filter_upwards with y
          exact div_nonneg (Complex.normSq_nonneg _) (sq_nonneg y)
        · exact hmajor
        · filter_upwards [ae_restrict_mem measurableSet_Ioi] with y hy
          convert div_le_div_of_nonneg_right
            (normSq_selbergExplicitInverseFourierKernel_le delta X y)
            (sq_nonneg y) using 1 <;> ring
    _ = 2 * (∫ y in Ioi L,
          Complex.normSq (selbergResidueInverseFourierKernel delta X y) /
            y ^ 2) +
        2 * (∫ y in Ioi L,
          Complex.normSq
            (selbergNonconstantInverseFourierKernel delta X y) / y ^ 2) := by
      rw [integral_add (hRint.const_mul 2) (hNint.const_mul 2),
        integral_const_mul, integral_const_mul]
    _ ≤ 2 * ((X : ℝ) ^ 4 / L ^ 2) + 2 * (C * S) := by
      gcongr
    _ = 2 * (X : ℝ) ^ 4 / Real.log ((X : ℝ) ^ a) ^ 2 +
        2 * C * (delta ^ (-(1 / 2 : ℝ)) /
          (Real.log ((X : ℝ) ^ a) * Real.log (X : ℝ))) := by
      dsimp [S, L, G]
      ring

end HardyTheorem
