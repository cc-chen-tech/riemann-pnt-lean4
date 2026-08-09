import HardyTheorem.SelbergSqrtZetaCollectedArithmetic
import HardyTheorem.SelbergSqrtZetaSignedRationalCoprimeRayCoeff

/-!
# Harmonic and logarithmic expansion on a signed Selberg coprime ray

The exact coefficient on the coprime ray `(a,b)` still contains two
square-root normalizations and two tapered coefficients.  The denominator
fiber relation `m*r = b*d` makes its square-root factor constant on the
fiber.  Combining it with the numerator normalization exposes the harmonic
scale weight `1/d`.

The resulting scale sum is a bilinear form in the numerator and denominator
coefficient functions.  Expanding both linear tapers writes it exactly as a
quadratic polynomial in `1 / log X`.  Thus the four arithmetic sums whose
cancellation is needed are separated without absolute values or
fiber-cardinality losses.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- The signed arithmetic coefficient left after removing the common
`1 / sqrt k` factor from a collected denominator fiber. -/
noncomputable def selbergSqrtZetaSignedDenominatorArithmeticCoeff
    (N X k : ℕ) : ℝ :=
  ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X k,
    selbergSqrtZetaTaperedCoeff X p.2

/-- The harmonic bilinear scale sum on the fixed ray `(a,b)`.  The first
function is evaluated at the numerator index `a*d`; the second is summed over
the denominator factorizations `m*r = b*d`. -/
noncomputable def selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
    (N X a b : ℕ) (u v : ℕ → ℝ) : ℝ :=
  ∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
    (d : ℝ)⁻¹ * u (a * d) *
      ∑ p ∈ selbergSqrtZetaSignedDenominatorFiber N X (b * d),
        v p.2

/-- On one denominator fiber, both square-root factors combine to the common
normalization `1 / sqrt k`. -/
theorem
    selbergSqrtZetaSignedDenominatorCollectedRealCoeff_eq_invSqrt_mul_arithmeticCoeff
    (N X k : ℕ) :
    selbergSqrtZetaSignedDenominatorCollectedRealCoeff N X k =
      (Real.sqrt k)⁻¹ *
        selbergSqrtZetaSignedDenominatorArithmeticCoeff N X k := by
  classical
  unfold selbergSqrtZetaSignedDenominatorCollectedRealCoeff
    selbergSqrtZetaSignedDenominatorArithmeticCoeff
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  have hkey : p.1 * p.2 = k := by
    exact (Finset.mem_filter.mp hp).2
  have hkeyReal : (p.1 : ℝ) * (p.2 : ℝ) = (k : ℝ) := by
    exact_mod_cast hkey
  calc
    selbergSqrtZetaTaperedCoeff X p.2 *
          (Real.sqrt p.1)⁻¹ * (Real.sqrt p.2)⁻¹ =
        selbergSqrtZetaTaperedCoeff X p.2 *
          (Real.sqrt p.1 * Real.sqrt p.2)⁻¹ := by
      rw [mul_inv]
      ring
    _ = selbergSqrtZetaTaperedCoeff X p.2 *
          (Real.sqrt ((p.1 : ℝ) * (p.2 : ℝ)))⁻¹ := by
      rw [Real.sqrt_mul (by positivity)]
    _ = selbergSqrtZetaTaperedCoeff X p.2 *
          (Real.sqrt k)⁻¹ := by rw [hkeyReal]
    _ = (Real.sqrt k)⁻¹ *
          selbergSqrtZetaTaperedCoeff X p.2 := by ring

private theorem invSqrt_mul_invSqrt_mul_eq_invSqrt_mul_invScale
    (a b d : ℕ) :
    (Real.sqrt (b * d))⁻¹ * (Real.sqrt (a * d))⁻¹ =
      (Real.sqrt (a * b))⁻¹ * (d : ℝ)⁻¹ := by
  have hsqrt :
      Real.sqrt (b * d) * Real.sqrt (a * d) =
        Real.sqrt (a * b) * (d : ℝ) := by
    rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ b),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a),
      Real.sqrt_mul (by positivity : (0 : ℝ) ≤ a)]
    calc
      √(b : ℝ) * √(d : ℝ) * (√(a : ℝ) * √(d : ℝ)) =
          √(a : ℝ) * √(b : ℝ) * (√(d : ℝ) * √(d : ℝ)) := by ring
      _ = √(a : ℝ) * √(b : ℝ) * (d : ℝ) := by
        rw [Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ d)]
  rw [← mul_inv, hsqrt, mul_inv]

/-- A pair coefficient on a fixed ray has the exact harmonic normalization
`1 / (sqrt(a*b) * d)`. -/
theorem
    selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_invSqrt_mul_invScale
    (N X a b d : ℕ) :
    selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d) =
      (Real.sqrt (a * b))⁻¹ * (d : ℝ)⁻¹ *
        (selbergSqrtZetaTaperedCoeff X (a * d) *
          selbergSqrtZetaSignedDenominatorArithmeticCoeff N X (b * d)) := by
  rw [selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq,
    selbergSqrtZetaSignedDenominatorCollectedRealCoeff_eq_invSqrt_mul_arithmeticCoeff]
  unfold selbergSqrtZetaSignedNumeratorRealCoeff
  push_cast
  calc
    (Real.sqrt (b * d))⁻¹ *
          selbergSqrtZetaSignedDenominatorArithmeticCoeff N X (b * d) *
          (selbergSqrtZetaTaperedCoeff X (a * d) *
            (Real.sqrt (a * d))⁻¹) =
        ((Real.sqrt (b * d))⁻¹ * (Real.sqrt (a * d))⁻¹) *
          (selbergSqrtZetaTaperedCoeff X (a * d) *
            selbergSqrtZetaSignedDenominatorArithmeticCoeff N X (b * d)) := by
      ring
    _ = (Real.sqrt (a * b))⁻¹ * (d : ℝ)⁻¹ *
          (selbergSqrtZetaTaperedCoeff X (a * d) *
            selbergSqrtZetaSignedDenominatorArithmeticCoeff N X (b * d)) := by
      rw [invSqrt_mul_invSqrt_mul_eq_invSqrt_mul_invScale]

/-- The whole fixed-ray scale sum is the harmonic bilinear form in the two
tapered coefficient functions, with only `1 / sqrt(a*b)` left outside. -/
theorem
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum
    (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) =
      (Real.sqrt (a * b))⁻¹ *
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
          (selbergSqrtZetaTaperedCoeff X)
          (selbergSqrtZetaTaperedCoeff X) := by
  classical
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [
    selbergSqrtZetaSignedRationalPairCoeff_coprimeRay_eq_invSqrt_mul_invScale]
  unfold selbergSqrtZetaSignedDenominatorArithmeticCoeff
  ring

/-- The linear taper is the untapered square-root-zeta coefficient minus its
logarithmic coefficient times `1 / log X`. -/
theorem selbergSqrtZetaTaperedCoeff_eq_coeff_sub_invLog_mul_logCoeff
    (X n : ℕ) :
    selbergSqrtZetaTaperedCoeff X n =
      selbergSqrtZetaCoeff n -
        (Real.log X)⁻¹ * selbergSqrtZetaLogCoeff n := by
  unfold selbergSqrtZetaTaperedCoeff selbergMoebiusWeight
  change
    selbergSqrtZetaCoeff n *
        (1 - Real.log n / Real.log X) =
      selbergSqrtZetaCoeff n -
        (Real.log X)⁻¹ *
          (selbergSqrtZetaCoeff n * Real.log n)
  rw [div_eq_mul_inv]
  ring

private theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_sub_left
    (N X a b : ℕ) (u₁ u₂ v : ℕ → ℝ) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
        (fun n => u₁ n - u₂ n) v =
      selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u₁ v -
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u₂ v := by
  classical
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_sub_right
    (N X a b : ℕ) (u v₁ v₂ : ℕ → ℝ) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u
        (fun n => v₁ n - v₂ n) =
      selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u v₁ -
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u v₂ := by
  classical
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.sum_sub_distrib]
  ring

private theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_left
    (N X a b : ℕ) (c : ℝ) (u v : ℕ → ℝ) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
        (fun n => c * u n) v =
      c * selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u v := by
  classical
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

private theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_right
    (N X a b : ℕ) (c : ℝ) (u v : ℕ → ℝ) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u
        (fun n => c * v n) =
      c * selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b u v := by
  classical
  unfold selbergSqrtZetaSignedCoprimeRayBilinearScaleSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← Finset.mul_sum]
  ring

/-- Bilinearity separates the two tapers into the untapered term, the two
single-log terms, and the double-log term. -/
theorem
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_taper_eq_logExpansion
    (N X a b : ℕ) :
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
        (selbergSqrtZetaTaperedCoeff X)
        (selbergSqrtZetaTaperedCoeff X) =
      selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
          selbergSqrtZetaCoeff selbergSqrtZetaCoeff -
        (Real.log X)⁻¹ *
          (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaLogCoeff selbergSqrtZetaCoeff +
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaCoeff selbergSqrtZetaLogCoeff) +
        (Real.log X)⁻¹ ^ 2 *
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            selbergSqrtZetaLogCoeff selbergSqrtZetaLogCoeff := by
  let c : ℝ := (Real.log X)⁻¹
  let A : ℕ → ℝ := selbergSqrtZetaCoeff
  let L : ℕ → ℝ := selbergSqrtZetaLogCoeff
  have htaper :
      selbergSqrtZetaTaperedCoeff X =
        fun n => A n - c * L n := by
    funext n
    exact
      selbergSqrtZetaTaperedCoeff_eq_coeff_sub_invLog_mul_logCoeff X n
  rw [htaper]
  calc
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
          (fun n => A n - c * L n) (fun n => A n - c * L n) =
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            A (fun n => A n - c * L n) -
          selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            (fun n => c * L n) (fun n => A n - c * L n) :=
      selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_sub_left
        N X a b A (fun n => c * L n) (fun n => A n - c * L n)
    _ =
        (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b A A -
          selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            A (fun n => c * L n)) -
        (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            (fun n => c * L n) A -
          selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            (fun n => c * L n) (fun n => c * L n)) := by
      rw [
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_sub_right,
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_sub_right]
    _ =
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b A A -
          c *
            (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b L A +
              selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b A L) +
          c ^ 2 *
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b L L := by
      rw [
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_right,
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_left,
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_left,
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_mul_right]
      ring
    _ =
        selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            selbergSqrtZetaCoeff selbergSqrtZetaCoeff -
          (Real.log X)⁻¹ *
            (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaLogCoeff selbergSqrtZetaCoeff +
              selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaCoeff selbergSqrtZetaLogCoeff) +
          (Real.log X)⁻¹ ^ 2 *
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaLogCoeff selbergSqrtZetaLogCoeff := by
      rfl

/-- Exact logarithmic expansion of the actual fixed-ray scale sum.  This is
the cancellation-ready form: each of the four arithmetic sums carries the
same harmonic `1/d` weight and no absolute-value or cardinality loss. -/
theorem selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_logExpansion
    (N X a b : ℕ) :
    (∑ d ∈ selbergSqrtZetaSignedCoprimeRayScaleSupport N X a b,
        selbergSqrtZetaSignedRationalPairCoeff N X (b * d, a * d)) =
      (Real.sqrt (a * b))⁻¹ *
        (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
            selbergSqrtZetaCoeff selbergSqrtZetaCoeff -
          (Real.log X)⁻¹ *
            (selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaLogCoeff selbergSqrtZetaCoeff +
              selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
                selbergSqrtZetaCoeff selbergSqrtZetaLogCoeff) +
          (Real.log X)⁻¹ ^ 2 *
            selbergSqrtZetaSignedCoprimeRayBilinearScaleSum N X a b
              selbergSqrtZetaLogCoeff selbergSqrtZetaLogCoeff) := by
  rw [
    selbergSqrtZetaSignedCoprimeRayScaleSum_eq_invSqrt_mul_bilinearScaleSum,
    selbergSqrtZetaSignedCoprimeRayBilinearScaleSum_taper_eq_logExpansion]

end HardyTheorem
