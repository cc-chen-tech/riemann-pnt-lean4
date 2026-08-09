import HardyTheorem.SelbergSqrtZetaSignedReducedPairCompleteCancellation

/-!
# Exact boxed-divisor normal form for the complete-product high energy

The complete product coefficient is collected over a finite square box.  This
file exposes that collection as a signed divisor-antidiagonal sum and extends
the high-product energy to the full interval `X < n ≤ X²`.  Terms outside the
product support vanish exactly; no absolute-value or fiber-cardinality bound is
used.
-/

open scoped BigOperators ArithmeticFunction

namespace HardyTheorem

/-- A positive product fiber in the complete square box is exactly the divisor
antidiagonal restricted to divisors whose two coordinates are at most `X`. -/
theorem selbergSqrtZetaCompleteProductFiber_eq_divisorsAntidiagonal_filter_box
    {X n : ℕ} (hn : 0 < n) :
    selbergSqrtZetaCompleteProductFiber X n =
      n.divisorsAntidiagonal.filter (fun p => p.1 ≤ X ∧ p.2 ≤ X) := by
  classical
  ext p
  constructor
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpBox, hpProd⟩
    rcases Finset.mem_product.mp hpBox with ⟨hp1, hp2⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hpProd, hn.ne'⟩,
        (Finset.mem_Icc.mp hp1).2, (Finset.mem_Icc.mp hp2).2⟩
  · intro hp
    rcases Finset.mem_filter.mp hp with ⟨hpDiv, hpBounds⟩
    rcases Nat.mem_divisorsAntidiagonal.mp hpDiv with ⟨hpProd, hn0⟩
    have hpProd0 : p.1 * p.2 ≠ 0 := by
      rw [hpProd]
      exact hn0
    have hp1 : 0 < p.1 :=
      Nat.pos_of_ne_zero (left_ne_zero_of_mul hpProd0)
    have hp2 : 0 < p.2 :=
      Nat.pos_of_ne_zero (right_ne_zero_of_mul hpProd0)
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨hp1, hpBounds.1⟩,
            Finset.mem_Icc.mpr ⟨hp2, hpBounds.2⟩⟩,
        hpProd⟩

/-- The product-collected coefficient is inverse square-root normalized times
the signed boxed divisor sum of the two full taper factors. -/
theorem selbergSqrtZetaCompleteProductCoeff_eq_invSqrt_mul_boxedDivisorSum
    {X n : ℕ} (hn : 0 < n) :
    selbergSqrtZetaCompleteProductCoeff X n =
      (Real.sqrt n)⁻¹ *
        ∑ p ∈ n.divisorsAntidiagonal.filter
            (fun p => p.1 ≤ X ∧ p.2 ≤ X),
          selbergSqrtZetaFullTapered X p.1 *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaFullTapered X) p.2) := by
  classical
  unfold selbergSqrtZetaCompleteProductCoeff
  rw [selbergSqrtZetaCompleteProductFiber_eq_divisorsAntidiagonal_filter_box hn,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpDiv, _hpBounds⟩
  have hpProd := (Nat.mem_divisorsAntidiagonal.mp hpDiv).1
  have hpProd0 : p.1 * p.2 ≠ 0 := by
    rw [hpProd]
    exact hn.ne'
  have hp1PosR : (0 : ℝ) < p.1 := by
    exact_mod_cast (Nat.pos_of_ne_zero (left_ne_zero_of_mul hpProd0))
  have hp2PosR : (0 : ℝ) < p.2 := by
    exact_mod_cast (Nat.pos_of_ne_zero (right_ne_zero_of_mul hpProd0))
  have hpProdR : (p.1 : ℝ) * (p.2 : ℝ) = (n : ℝ) := by
    exact_mod_cast hpProd
  have hp1nonneg : (0 : ℝ) ≤ p.1 := by positivity
  have hsqrt : Real.sqrt n = Real.sqrt p.1 * Real.sqrt p.2 := by
    rw [← Real.sqrt_mul hp1nonneg, hpProdR]
  unfold selbergSqrtZetaCompletePairCoeff
    selbergSqrtZetaCompleteNumeratorCoeff
    selbergSqrtZetaCompleteDenominatorCoeff
  rw [hsqrt]
  field_simp [Real.sqrt_ne_zero'.mpr hp1PosR,
    Real.sqrt_ne_zero'.mpr hp2PosR]

/-- Exact boxed-divisor normal form for the high-product energy.  The original
product support is extended by zero to every integer `X < n ≤ X²`, while the
signed divisor sum remains intact inside the square. -/
theorem selbergSqrtZetaCompleteProductHighEnergy_eq_boxedDivisorEnergy
    (X : ℕ) :
    selbergSqrtZetaCompleteProductHighEnergy X =
      ∑ n ∈ Finset.Ioc X (X * X),
        (∑ p ∈ n.divisorsAntidiagonal.filter
            (fun p => p.1 ≤ X ∧ p.2 ≤ X),
          selbergSqrtZetaFullTapered X p.1 *
            (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
              selbergSqrtZetaFullTapered X) p.2)) ^ 2 / (n : ℝ) := by
  classical
  let S := (selbergSqrtZetaCompleteProductSupport X).filter (fun n => X < n)
  let F : ℕ → ℝ := fun n =>
    (∑ p ∈ n.divisorsAntidiagonal.filter
        (fun p => p.1 ≤ X ∧ p.2 ≤ X),
      selbergSqrtZetaFullTapered X p.1 *
        (((ArithmeticFunction.zeta : ArithmeticFunction ℝ) *
          selbergSqrtZetaFullTapered X) p.2)) ^ 2 / (n : ℝ)
  have hS : S ⊆ Finset.Ioc X (X * X) := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnSupport, hXn⟩
    rcases Finset.mem_image.mp hnSupport with ⟨p, hpBox, rfl⟩
    rcases Finset.mem_product.mp hpBox with ⟨hp1, hp2⟩
    exact Finset.mem_Ioc.mpr
      ⟨hXn, Nat.mul_le_mul (Finset.mem_Icc.mp hp1).2
        (Finset.mem_Icc.mp hp2).2⟩
  have hzero :
      ∀ n ∈ Finset.Ioc X (X * X), n ∉ S → F n = 0 := by
    intro n hnRange hnS
    have hnNotSupport : n ∉ selbergSqrtZetaCompleteProductSupport X := by
      intro hnSupport
      exact hnS (Finset.mem_filter.mpr
        ⟨hnSupport, (Finset.mem_Ioc.mp hnRange).1⟩)
    have hfiber :
        n.divisorsAntidiagonal.filter
            (fun p => p.1 ≤ X ∧ p.2 ≤ X) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hpDiv, hpBounds⟩
      rcases Nat.mem_divisorsAntidiagonal.mp hpDiv with ⟨hpProd, hn0⟩
      have hpProd0 : p.1 * p.2 ≠ 0 := by
        rw [hpProd]
        exact hn0
      have hpPair : p ∈ selbergSqrtZetaCompletePairSupport X :=
        Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr
              ⟨Nat.pos_of_ne_zero (left_ne_zero_of_mul hpProd0), hpBounds.1⟩,
            Finset.mem_Icc.mpr
              ⟨Nat.pos_of_ne_zero (right_ne_zero_of_mul hpProd0), hpBounds.2⟩⟩
      apply hnNotSupport
      exact Finset.mem_image.mpr ⟨p, hpPair, hpProd⟩
    unfold F
    rw [hfiber]
    simp
  have hcoeff (n : ℕ) (hn : n ∈ S) :
      selbergSqrtZetaCompleteProductCoeff X n ^ 2 = F n := by
    have hnPos : 0 < n := by
      have hXn := (Finset.mem_filter.mp hn).2
      omega
    rw [selbergSqrtZetaCompleteProductCoeff_eq_invSqrt_mul_boxedDivisorSum hnPos]
    unfold F
    have hsqrt : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [mul_pow, inv_pow, hsqrt, div_eq_mul_inv]
    ring
  unfold selbergSqrtZetaCompleteProductHighEnergy
  change (∑ n ∈ S, selbergSqrtZetaCompleteProductCoeff X n ^ 2) =
    ∑ n ∈ Finset.Ioc X (X * X), F n
  rw [show (∑ n ∈ S, selbergSqrtZetaCompleteProductCoeff X n ^ 2) =
      ∑ n ∈ S, F n by
    apply Finset.sum_congr rfl
    intro n hn
    exact hcoeff n hn]
  exact Finset.sum_subset hS hzero

end HardyTheorem
