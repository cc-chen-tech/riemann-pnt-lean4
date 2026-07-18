import ZeroFreeRegion.VinogradovKorobov.FirstDerivative

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

example (x : ℝ) (hx : Real.sin (x / 2) ≠ 0) :
    (Complex.exp (Complex.I * (x : ℂ)) - 1)⁻¹ =
      (-1 / 2 : ℂ) - Complex.I * (Real.cot (x / 2) / 2 : ℝ) :=
  reciprocal_exp_sub_one_eq x hx

example {a b : ℝ} (ha : 0 < a) (hb : b < Real.pi) :
    AntitoneOn Real.cot (Set.Icc a b) :=
  antitoneOn_cot_Icc ha hb

example {x y : ℝ} (hx : 0 < x) (hy : y < 2 * Real.pi) (hxy : x ≤ y) :
    ‖(Complex.exp (Complex.I * (x : ℂ)) - 1)⁻¹ -
        (Complex.exp (Complex.I * (y : ℂ)) - 1)⁻¹‖ =
      (Real.cot (x / 2) - Real.cot (y / 2)) / 2 :=
  norm_reciprocal_exp_sub_one_sub_eq hx hy hxy

example (theta : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < theta k)
    (hlt : ∀ k ≤ N, theta k < 2 * Real.pi)
    (hmono : ∀ k < N, theta k ≤ theta (k + 1)) :
    ∑ k ∈ Finset.range N,
        ‖(Complex.exp (Complex.I * (theta k : ℂ)) - 1)⁻¹ -
          (Complex.exp (Complex.I * (theta (k + 1) : ℂ)) - 1)⁻¹‖ =
      (Real.cot (theta 0 / 2) - Real.cot (theta N / 2)) / 2 :=
  sum_norm_reciprocal_exp_sub_one_eq theta N hpos hlt hmono

example (d z : ℕ → ℂ) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), d k * (z (k + 1) - z k) =
      d N * z (N + 1) - d 0 * z 0 +
        ∑ k ∈ Finset.range N, (d k - d (k + 1)) * z (k + 1) :=
  sum_range_mul_forwardDifference d z N

example (q z : ℕ → ℂ) (N : ℕ)
    (hq : ∀ k ≤ N, q k ≠ 1)
    (hzstep : ∀ k ≤ N, z (k + 1) = q k * z k)
    (hznorm : ∀ k ≤ N + 1, ‖z k‖ ≤ 1) :
    ‖∑ k ∈ Finset.range (N + 1), z k‖ ≤
      ‖(q 0 - 1)⁻¹‖ + ‖(q N - 1)⁻¹‖ +
        ∑ k ∈ Finset.range N,
          ‖(q k - 1)⁻¹ - (q (k + 1) - 1)⁻¹‖ :=
  norm_sum_range_le_reciprocalVariation q z N hq hzstep hznorm

example (f : ℕ → ℝ) (k : ℕ) :
    phaseTerm f (k + 1) = phaseRatio f k * phaseTerm f k :=
  phaseTerm_succ_eq_phaseRatio_mul f k

example (f : ℕ → ℝ) (k : ℕ)
    (hpos : 0 < f (k + 1) - f k)
    (hlt : f (k + 1) - f k < 2 * Real.pi) :
    phaseRatio f k ≠ 1 :=
  phaseRatio_ne_one_of_increment_mem f k hpos hlt

example (f : ℕ → ℝ) (N : ℕ)
    (hq : ∀ k ≤ N, phaseRatio f k ≠ 1) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      ‖(phaseRatio f 0 - 1)⁻¹‖ + ‖(phaseRatio f N - 1)⁻¹‖ +
        ∑ k ∈ Finset.range N,
          ‖(phaseRatio f k - 1)⁻¹ - (phaseRatio f (k + 1) - 1)⁻¹‖ :=
  norm_phaseSum_le_reciprocalVariation f N hq

example (f : ℕ → ℝ) (N : ℕ)
    (hpos : ∀ k ≤ N, 0 < f (k + 1) - f k)
    (hlt : ∀ k ≤ N, f (k + 1) - f k < 2 * Real.pi)
    (hmono : ∀ k < N,
      f (k + 1) - f k ≤ f (k + 2) - f (k + 1)) :
    ‖∑ k ∈ Finset.range (N + 1), phaseTerm f k‖ ≤
      ‖(Complex.exp (Complex.I * ((f 1 - f 0 : ℝ) : ℂ)) - 1)⁻¹‖ +
      ‖(Complex.exp (Complex.I * ((f (N + 1) - f N : ℝ) : ℂ)) - 1)⁻¹‖ +
      (Real.cot ((f 1 - f 0) / 2) -
        Real.cot ((f (N + 1) - f N) / 2)) / 2 :=
  kusminLandau_endpoint_bound f N hpos hlt hmono

end ZeroFreeRegion.VinogradovKorobov
