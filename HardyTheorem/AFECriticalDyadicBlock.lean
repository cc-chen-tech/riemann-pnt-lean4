import HardyTheorem.SelbergMollifiedDirichlet
import HardyTheorem.SelbergMollifiedGaussianPolynomial
import MathlibAux.FiberwiseNormSq

/-!
# Coefficient energy for dyadic AFE blocks

At a fixed dyadic level, division by the block length assigns every zeta
index to a unique aligned block.  Applying finite Cauchy--Schwarz along these
owner-map fibres proves the coefficient form of the levelwise
Rademacher--Menshov estimate.
-/

open Complex
open scoped BigOperators ArithmeticFunction
open PrimeNumberTheorem.CarlsonZeroDensity

namespace HardyTheorem
namespace AFE

/-- Factor pairs used by all dyadic blocks inside the ambient prefix of
length `2^K`.  The upper endpoint is excluded so that every owner is strictly
below `2^K`, uniformly in the dyadic level. -/
noncomputable def dyadicMollifiedFactorPairs
    (K X k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Ico 1 (2 ^ K)).product (Finset.Icc 1 X)).filter
    (fun p => p.1 * p.2 = k)

/-- Collected convolution coefficient belonging to the aligned block whose
owner index is `q` at level `j`. -/
noncomputable def dyadicMollifiedBlockCoeff
    (K j X k q : ℕ) : ℂ :=
  ∑ p ∈ (dyadicMollifiedFactorPairs K X k).filter
      (fun p => p.1 / 2 ^ j = q),
    (selbergMoebiusCoeff X p.2 : ℂ)

private theorem dyadicMollifiedFactorPairs_subset_divisorsAntidiagonal
    (K X k : ℕ) :
    dyadicMollifiedFactorPairs K X k ⊆ k.divisorsAntidiagonal := by
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpProd, hprod⟩
  rcases Finset.mem_product.mp hpProd with ⟨hpn, hpd⟩
  rw [Nat.mem_divisorsAntidiagonal]
  have hp1ne : p.1 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt (Finset.mem_Ico.mp hpn).1)
  have hp2ne : p.2 ≠ 0 := by
    exact Nat.ne_of_gt (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hpd).1)
  exact ⟨hprod, hprod ▸ Nat.mul_ne_zero hp1ne hp2ne⟩

/-- At a fixed dyadic level and product index `k`, the sum of collected
coefficient squares over all aligned owners is at most `d(k)^2`.

This is equation (8.4) before inserting the critical-line weight `1/k`.
The owner range `q < 2^K` is deliberately uniform in `j`; owners outside the
actual level are empty and therefore cost no energy. -/
theorem sum_normSq_dyadicMollifiedBlockCoeff_le
    {K j X k : ℕ} (hX : 2 ≤ X) :
    (∑ q ∈ Finset.range (2 ^ K),
        Complex.normSq (dyadicMollifiedBlockCoeff K j X k q)) ≤
      (k.divisorsAntidiagonal.card : ℝ) ^ 2 := by
  classical
  let S := dyadicMollifiedFactorPairs K X k
  let Q := Finset.range (2 ^ K)
  let owner : ℕ × ℕ → ℕ := fun p => p.1 / 2 ^ j
  let coeff : ℕ × ℕ → ℂ := fun p => (selbergMoebiusCoeff X p.2 : ℂ)
  let D : ℝ := k.divisorsAntidiagonal.card
  have hmaps : ∀ p ∈ S, owner p ∈ Q := by
    intro p hp
    have hpS : p ∈ dyadicMollifiedFactorPairs K X k := hp
    have hpn := (Finset.mem_product.mp (Finset.mem_filter.mp hpS).1).1
    exact Finset.mem_range.mpr <|
      (Nat.div_le_self p.1 (2 ^ j)).trans_lt (Finset.mem_Ico.mp hpn).2
  have hcard : ∀ q ∈ Q,
      (((S.filter fun p => owner p = q).card : ℕ) : ℝ) ≤ D := by
    intro q hq
    have hsub : S.filter (fun p => owner p = q) ⊆
        k.divisorsAntidiagonal := by
      intro p hp
      exact dyadicMollifiedFactorPairs_subset_divisorsAntidiagonal K X k
        (Finset.mem_filter.mp hp).1
    change ((S.filter fun p => owner p = q).card : ℝ) ≤
      (k.divisorsAntidiagonal.card : ℝ)
    exact_mod_cast Finset.card_le_card hsub
  have henergy : (∑ p ∈ S, Complex.normSq (coeff p)) ≤ D := by
    calc
      (∑ p ∈ S, Complex.normSq (coeff p)) ≤ ∑ _p ∈ S, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpS : p ∈ dyadicMollifiedFactorPairs K X k := hp
        have hpd := (Finset.mem_product.mp (Finset.mem_filter.mp hpS).1).2
        have habs := abs_selbergMoebiusCoeff_le_one hX
          (Finset.mem_Icc.mp hpd).1 (Finset.mem_Icc.mp hpd).2
        change Complex.normSq (selbergMoebiusCoeff X p.2 : ℂ) ≤ 1
        rw [Complex.normSq_ofReal]
        rcases abs_le.mp habs with ⟨hlow, hup⟩
        nlinarith [mul_nonneg
          (show 0 ≤ selbergMoebiusCoeff X p.2 + 1 by linarith)
          (show 0 ≤ 1 - selbergMoebiusCoeff X p.2 by linarith)]
      _ = (S.card : ℝ) := by simp
      _ ≤ D := by
        change (S.card : ℝ) ≤ (k.divisorsAntidiagonal.card : ℝ)
        exact_mod_cast Finset.card_le_card
          (dyadicMollifiedFactorPairs_subset_divisorsAntidiagonal K X k)
  have hbase := MathlibAux.sum_normSq_fiber_le_sq
    S Q owner coeff hmaps (by positivity : 0 ≤ D) hcard henergy
  simpa only [S, Q, owner, coeff, D, dyadicMollifiedBlockCoeff] using hbase

/-- Critical-line coefficient of one collected dyadic block. -/
noncomputable def dyadicMollifiedCriticalBlockCoeff
    (K j X k q : ℕ) : ℂ :=
  dyadicMollifiedBlockCoeff K j X k q *
    ((Real.sqrt k : ℂ)⁻¹)

/-- Equation (8.4) with the critical-line `1/k` weight retained. -/
theorem sum_normSq_dyadicMollifiedCriticalBlockCoeff_le
    {K j X k : ℕ} (hX : 2 ≤ X) (hk : 0 < k) :
    (∑ q ∈ Finset.range (2 ^ K),
        Complex.normSq
          (dyadicMollifiedCriticalBlockCoeff K j X k q)) ≤
      (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
  have hweight :
      Complex.normSq ((Real.sqrt k : ℂ)⁻¹) = (k : ℝ)⁻¹ := by
    rw [Complex.normSq_inv, Complex.normSq_ofReal,
      Real.mul_self_sqrt (by positivity)]
  have hraw := sum_normSq_dyadicMollifiedBlockCoeff_le
    (K := K) (j := j) (k := k) hX
  have hdiv := card_divisorsAntidiagonal_sq_le_fourfoldDivisorCount hk.ne'
  calc
    (∑ q ∈ Finset.range (2 ^ K),
        Complex.normSq
          (dyadicMollifiedCriticalBlockCoeff K j X k q)) =
        (∑ q ∈ Finset.range (2 ^ K),
          Complex.normSq (dyadicMollifiedBlockCoeff K j X k q)) *
            (k : ℝ)⁻¹ := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro q hq
      rw [dyadicMollifiedCriticalBlockCoeff,
        Complex.normSq_mul, hweight]
    _ ≤ (k.divisorsAntidiagonal.card : ℝ) ^ 2 * (k : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_right hraw (by positivity)
    _ ≤ (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast hdiv
      · positivity

/-- The collected critical-line coefficient energy of one complete dyadic
level is polylogarithmic, uniformly in the level. -/
theorem sum_levelEnergy_dyadicMollifiedCriticalBlockCoeff_le
    {K j X : ℕ} (hX : 2 ≤ X) :
    (∑ k ∈ Finset.Icc 1 (2 ^ K * X),
        ∑ q ∈ Finset.range (2 ^ K),
          Complex.normSq
            (dyadicMollifiedCriticalBlockCoeff K j X k q)) ≤
      2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4 := by
  have hU : 1 ≤ 2 ^ K * X := by
    exact Nat.one_le_iff_ne_zero.mpr
      (Nat.mul_ne_zero (pow_ne_zero K (by norm_num)) (by omega))
  calc
    (∑ k ∈ Finset.Icc 1 (2 ^ K * X),
        ∑ q ∈ Finset.range (2 ^ K),
          Complex.normSq
            (dyadicMollifiedCriticalBlockCoeff K j X k q)) ≤
      ∑ k ∈ Finset.Icc 1 (2 ^ K * X),
        (fourfoldDivisorCount k : ℝ) * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      exact sum_normSq_dyadicMollifiedCriticalBlockCoeff_le hX
        (Nat.zero_lt_of_lt (Finset.mem_Icc.mp hk).1)
    _ ≤ 2 * (1 + Real.log (((2 ^ K * X : ℕ) : ℝ))) ^ 4 :=
      fourfoldDivisor_inv_sum_le_two_mul_log_pow_four hU

end AFE
end HardyTheorem
