import PrimeNumberTheorem.QPowerDetectorAlgebra

open Polynomial
open scoped BigOperators

namespace PrimeNumberTheorem
namespace PrimeSideDetector

noncomputable section

/-- Positive weighted coefficient mass of a real polynomial at `r`.
It has the intended mass interpretation when `0 ≤ r`. -/
def polynomialPositiveMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (p.coeff k) 0 * r ^ k

/-- Negative weighted coefficient mass of a real polynomial at `r`.
It has the intended mass interpretation when `0 ≤ r`. -/
def polynomialNegativeMassAt (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, max (-p.coeff k) 0 * r ^ k

/-- Weighted coefficient `L¹` mass of a real polynomial at `r`.
It is nonnegative when `0 ≤ r`. -/
def polynomialWeightedL1At (r : Real) (p : Polynomial Real) : Real :=
  ∑ k ∈ p.support, |p.coeff k| * r ^ k

private theorem eq_max_sub_max_neg (x : Real) :
    x = max x 0 - max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

private theorem abs_eq_max_add_max_neg (x : Real) :
    |x| = max x 0 + max (-x) 0 := by
  by_cases hx : 0 ≤ x
  · rw [abs_of_nonneg hx, max_eq_left hx, max_eq_right (neg_nonpos.mpr hx)]
    simp
  · have hx' : x ≤ 0 := le_of_not_ge hx
    rw [abs_of_nonpos hx', max_eq_right hx', max_eq_left (neg_nonneg.mpr hx')]
    ring

/-- Polynomial evaluation is positive weighted mass minus negative weighted
mass. -/
theorem polynomial_eval_eq_positive_sub_negative
    (r : Real) (p : Polynomial Real) :
    p.eval r = polynomialPositiveMassAt r p -
      polynomialNegativeMassAt r p := by
  rw [p.eval_eq_sum]
  unfold polynomialPositiveMassAt polynomialNegativeMassAt
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← sub_mul, ← eq_max_sub_max_neg]

private theorem polynomialWeightedL1At_eq_positive_add_negative
    (r : Real) (p : Polynomial Real) :
    polynomialWeightedL1At r p =
      polynomialPositiveMassAt r p + polynomialNegativeMassAt r p := by
  unfold polynomialWeightedL1At polynomialPositiveMassAt polynomialNegativeMassAt
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← add_mul, ← abs_eq_max_add_max_neg]

/-- At a nonnegative real zero, negative weighted mass is exactly half the
weighted coefficient `L¹` mass. -/
theorem polynomialNegativeMassAt_eq_half_weightedL1At
    {r : Real} {p : Polynomial Real} (_hr : 0 ≤ r) (hzero : p.eval r = 0) :
    polynomialNegativeMassAt r p = polynomialWeightedL1At r p / 2 := by
  have hbalance :
      polynomialPositiveMassAt r p = polynomialNegativeMassAt r p := by
    rw [polynomial_eval_eq_positive_sub_negative] at hzero
    linarith
  rw [polynomialWeightedL1At_eq_positive_add_negative, hbalance]
  ring

private theorem evalRealPolynomial_ofReal
    (p : Polynomial Real) (r : Real) :
    evalRealPolynomial p r = p.eval r := by
  rw [evalRealPolynomial, ← Polynomial.eval₂_eq_eval_map]
  change p.eval₂ Complex.ofRealHom (Complex.ofRealHom r) =
    Complex.ofRealHom (p.eval r)
  rw [Polynomial.eval₂_at_apply]

/-- The normalized q-power detector cancels the main node, so its negative
coefficient mass there is exactly half its weighted `L¹` mass. -/
theorem normalizedQPowerPolynomial_negativeMass_eq_half
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex} (hq : q ≠ 0) :
    polynomialNegativeMassAt ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) =
      polynomialWeightedL1At ((q : Real)⁻¹)
        (normalizedQPowerPolynomial q realNodes pairNodes z0) / 2 := by
  apply polynomialNegativeMassAt_eq_half_weightedL1At
  · positivity
  · have hmain := normalizedQPowerPolynomial_eval_main
      (q := q) (realNodes := realNodes) (pairNodes := pairNodes)
      (z0 := z0) hq
    rw [← Complex.ofReal_inv] at hmain
    rw [evalRealPolynomial_ofReal] at hmain
    exact_mod_cast hmain

private theorem polynomialWeightedL1At_nonneg
    {r : Real} (hr : 0 ≤ r) (p : Polynomial Real) :
    0 ≤ polynomialWeightedL1At r p := by
  unfold polynomialWeightedL1At
  exact Finset.sum_nonneg fun k hk => mul_nonneg (abs_nonneg _) (pow_nonneg hr _)

private theorem polynomialWeightedL1At_monomial
    (r : Real) (n : Nat) (a : Real) :
    polynomialWeightedL1At r (monomial n a) = |a| * r ^ n := by
  change (monomial n a).sum (fun k c => |c| * r ^ k) = |a| * r ^ n
  simp

private theorem polynomialWeightedL1At_add_le
    {r : Real} (hr : 0 ≤ r) (p q : Polynomial Real) :
    polynomialWeightedL1At r (p + q) ≤
      polynomialWeightedL1At r p + polynomialWeightedL1At r q := by
  let f : Nat → Real → Real := fun k c => |c| * r ^ k
  change (p + q).sum f ≤ p.sum f + q.sum f
  have hf : ∀ i, f i 0 = 0 := by
    intro i
    simp [f]
  rw [(p + q).sum_eq_of_subset f hf support_add,
    p.sum_eq_of_subset f hf Finset.subset_union_left,
    q.sum_eq_of_subset f hf Finset.subset_union_right,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k hk
  dsimp [f]
  rw [coeff_add]
  simpa [add_mul] using
    mul_le_mul_of_nonneg_right (abs_add_le (p.coeff k) (q.coeff k))
      (pow_nonneg hr k)

private theorem polynomialWeightedL1At_finset_sum_le
    {ι : Type*} {r : Real} (hr : 0 ≤ r) (s : Finset ι)
    (p : ι → Polynomial Real) :
    polynomialWeightedL1At r (∑ i ∈ s, p i) ≤
      ∑ i ∈ s, polynomialWeightedL1At r (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [polynomialWeightedL1At]
  | @insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      exact (polynomialWeightedL1At_add_le hr _ _).trans
        (add_le_add le_rfl ih)

/-- Weighted coefficient `L¹` is submultiplicative at nonnegative weights. -/
theorem polynomialWeightedL1At_mul_le
    {r : Real} (hr : 0 ≤ r) (p q : Polynomial Real) :
    polynomialWeightedL1At r (p * q) ≤
      polynomialWeightedL1At r p * polynomialWeightedL1At r q := by
  rw [Polynomial.mul_eq_sum_sum]
  calc
    polynomialWeightedL1At r
        (∑ i ∈ p.support,
          q.sum fun j a => monomial (i + j) (p.coeff i * a)) ≤
        ∑ i ∈ p.support,
          polynomialWeightedL1At r
            (q.sum fun j a => monomial (i + j) (p.coeff i * a)) :=
      polynomialWeightedL1At_finset_sum_le hr _ _
    _ ≤ ∑ i ∈ p.support, ∑ j ∈ q.support,
          polynomialWeightedL1At r
            (monomial (i + j) (p.coeff i * q.coeff j)) := by
      apply Finset.sum_le_sum
      intro i hi
      rw [Polynomial.sum_def]
      exact polynomialWeightedL1At_finset_sum_le hr _ _
    _ = polynomialWeightedL1At r p * polynomialWeightedL1At r q := by
      simp_rw [polynomialWeightedL1At_monomial, abs_mul, pow_add]
      unfold polynomialWeightedL1At
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      ring

/-- A real linear zero factor has weighted coefficient mass at most
`r + |u|`. -/
theorem polynomialWeightedL1At_realNodeFactor_le
    {r : Real} (hr : 0 ≤ r) (u : Real) :
    polynomialWeightedL1At r (realNodeFactor u) ≤ r + |u| := by
  have h := polynomialWeightedL1At_add_le hr X (-C u)
  have hX : polynomialWeightedL1At r X = r := by
    rw [← monomial_one_one_eq_X, polynomialWeightedL1At_monomial]
    simp
  have hC : polynomialWeightedL1At r (-C u) = |u| := by
    rw [← C_neg, ← monomial_zero_left, polynomialWeightedL1At_monomial]
    simp
  rw [realNodeFactor, sub_eq_add_neg]
  simpa [hX, hC] using h

/-- A real quadratic conjugate-pair factor has weighted coefficient mass at
most `(r + ‖z‖)²`. -/
theorem polynomialWeightedL1At_conjugatePairFactor_le
    {r : Real} (hr : 0 ≤ r) (z : Complex) :
    polynomialWeightedL1At r (conjugatePairFactor z) ≤ (r + ‖z‖) ^ 2 := by
  have houter := polynomialWeightedL1At_add_le hr
    (X ^ 2 - C (2 * z.re) * X) (C (Complex.normSq z))
  have hinner := polynomialWeightedL1At_add_le hr
    (X ^ 2) (-(C (2 * z.re) * X))
  have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
  have hnormSq : Complex.normSq z = ‖z‖ ^ 2 := Complex.normSq_eq_norm_sq z
  have hX2 : polynomialWeightedL1At r (X ^ 2) = r ^ 2 := by
    rw [← monomial_one_right_eq_X_pow, polynomialWeightedL1At_monomial]
    simp
  have hlinear :
      polynomialWeightedL1At r (-(C (2 * z.re) * X)) =
        2 * |z.re| * r := by
    rw [C_mul_X_eq_monomial, ← monomial_neg,
      polynomialWeightedL1At_monomial]
    rw [abs_neg, abs_mul]
    norm_num
  have hconstant :
      polynomialWeightedL1At r (C (Complex.normSq z)) = Complex.normSq z := by
    rw [← monomial_zero_left, polynomialWeightedL1At_monomial]
    simp [Complex.normSq_nonneg]
  have hcalc :
      polynomialWeightedL1At r (X ^ 2 - C (2 * z.re) * X) ≤
        r ^ 2 + 2 * |z.re| * r := by
    calc
      polynomialWeightedL1At r (X ^ 2 - C (2 * z.re) * X) =
          polynomialWeightedL1At r (X ^ 2 + -(C (2 * z.re) * X)) := by
            rw [sub_eq_add_neg]
      _ ≤ polynomialWeightedL1At r (X ^ 2) +
          polynomialWeightedL1At r (-(C (2 * z.re) * X)) := hinner
      _ = r ^ 2 + 2 * |z.re| * r := by
        rw [hX2, hlinear]
  calc
    polynomialWeightedL1At r (conjugatePairFactor z) ≤
        polynomialWeightedL1At r (X ^ 2 - C (2 * z.re) * X) +
          polynomialWeightedL1At r (C (Complex.normSq z)) := by
      simpa [conjugatePairFactor] using houter
    _ ≤ (r ^ 2 + 2 * |z.re| * r) + Complex.normSq z := by
      exact add_le_add hcalc hconstant.le
    _ ≤ (r + ‖z‖) ^ 2 := by
      rw [hnormSq]
      nlinarith [mul_le_mul_of_nonneg_right hre hr]

private theorem polynomialWeightedL1At_finset_prod_le
    {ι : Type*} {r : Real} (hr : 0 ≤ r) (s : Finset ι)
    (p : ι → Polynomial Real) :
    polynomialWeightedL1At r (∏ i ∈ s, p i) ≤
      ∏ i ∈ s, polynomialWeightedL1At r (p i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      rw [Finset.prod_empty, Finset.prod_empty, ← monomial_zero_one,
        polynomialWeightedL1At_monomial]
      simp
  | @insert a s ha ih =>
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      exact (polynomialWeightedL1At_mul_le hr _ _).trans
        (mul_le_mul_of_nonneg_left ih (polynomialWeightedL1At_nonneg hr _))

/-- Factorized weighted coefficient-loss bound for the normalized q-power
detector polynomial.  A numerical bound additionally requires control of the
real interpolation factor. -/
theorem normalizedQPowerPolynomial_weightedL1_le
    {q : Nat} {realNodes : Finset Real} {pairNodes : Finset Complex}
    {z0 : Complex} {r : Real} (hr : 0 ≤ r) :
    polynomialWeightedL1At r
        (normalizedQPowerPolynomial q realNodes pairNodes z0) ≤
      polynomialWeightedL1At r
          (realLinearInterpolator z0
            (evalRealPolynomial
              (qPowerAnnihilator q realNodes pairNodes) z0)⁻¹) *
        (r + ((q : Real)⁻¹)) *
        (∏ u ∈ realNodes, (r + |u|)) *
        (∏ z ∈ pairNodes, (r + ‖z‖) ^ 2) := by
  let I := realLinearInterpolator z0
    (evalRealPolynomial (qPowerAnnihilator q realNodes pairNodes) z0)⁻¹
  let M := realNodeFactor ((q : Real)⁻¹)
  let R := ∏ u ∈ realNodes, realNodeFactor u
  let P := ∏ z ∈ pairNodes, conjugatePairFactor z
  have hM : polynomialWeightedL1At r M ≤ r + ((q : Real)⁻¹) := by
    simpa [M, abs_of_nonneg (by positivity : (0 : Real) ≤ (q : Real)⁻¹)] using
      polynomialWeightedL1At_realNodeFactor_le hr ((q : Real)⁻¹)
  have hR : polynomialWeightedL1At r R ≤ ∏ u ∈ realNodes, (r + |u|) := by
    calc
      polynomialWeightedL1At r R ≤
          ∏ u ∈ realNodes, polynomialWeightedL1At r (realNodeFactor u) :=
        polynomialWeightedL1At_finset_prod_le hr _ _
      _ ≤ ∏ u ∈ realNodes, (r + |u|) := by
        apply Finset.prod_le_prod
        · intro u hu
          exact polynomialWeightedL1At_nonneg hr _
        · intro u hu
          exact polynomialWeightedL1At_realNodeFactor_le hr u
  have hP : polynomialWeightedL1At r P ≤
      ∏ z ∈ pairNodes, (r + ‖z‖) ^ 2 := by
    calc
      polynomialWeightedL1At r P ≤
          ∏ z ∈ pairNodes,
            polynomialWeightedL1At r (conjugatePairFactor z) :=
        polynomialWeightedL1At_finset_prod_le hr _ _
      _ ≤ ∏ z ∈ pairNodes, (r + ‖z‖) ^ 2 := by
        apply Finset.prod_le_prod
        · intro z hz
          exact polynomialWeightedL1At_nonneg hr _
        · intro z hz
          exact polynomialWeightedL1At_conjugatePairFactor_le hr z
  have hMRP : polynomialWeightedL1At r (M * R * P) ≤
      (r + ((q : Real)⁻¹)) *
        (∏ u ∈ realNodes, (r + |u|)) *
        (∏ z ∈ pairNodes, (r + ‖z‖) ^ 2) := by
    calc
      polynomialWeightedL1At r (M * R * P) ≤
          polynomialWeightedL1At r (M * R) *
            polynomialWeightedL1At r P :=
        polynomialWeightedL1At_mul_le hr _ _
      _ ≤ (polynomialWeightedL1At r M * polynomialWeightedL1At r R) *
            polynomialWeightedL1At r P := by
        exact mul_le_mul_of_nonneg_right
          (polynomialWeightedL1At_mul_le hr M R)
          (polynomialWeightedL1At_nonneg hr P)
      _ ≤ (r + ((q : Real)⁻¹)) *
          (∏ u ∈ realNodes, (r + |u|)) *
          (∏ z ∈ pairNodes, (r + ‖z‖) ^ 2) := by
        have hmainNonneg : 0 ≤ r + ((q : Real)⁻¹) := by positivity
        have hrealNonneg : 0 ≤ ∏ u ∈ realNodes, (r + |u|) := by positivity
        exact mul_le_mul
          (mul_le_mul hM hR (polynomialWeightedL1At_nonneg hr _) hmainNonneg)
          hP (polynomialWeightedL1At_nonneg hr _) (mul_nonneg hmainNonneg hrealNonneg)
  unfold normalizedQPowerPolynomial qPowerAnnihilator
  change polynomialWeightedL1At r ((M * R * P) * I) ≤ _
  calc
    polynomialWeightedL1At r ((M * R * P) * I) ≤
        polynomialWeightedL1At r (M * R * P) *
          polynomialWeightedL1At r I :=
      polynomialWeightedL1At_mul_le hr _ _
    _ ≤ ((r + ((q : Real)⁻¹)) *
          (∏ u ∈ realNodes, (r + |u|)) *
          (∏ z ∈ pairNodes, (r + ‖z‖) ^ 2)) *
        polynomialWeightedL1At r I :=
      mul_le_mul_of_nonneg_right hMRP (polynomialWeightedL1At_nonneg hr _)
    _ = polynomialWeightedL1At r I *
        (r + ((q : Real)⁻¹)) *
        (∏ u ∈ realNodes, (r + |u|)) *
        (∏ z ∈ pairNodes, (r + ‖z‖) ^ 2) := by ring

end

end PrimeSideDetector
end PrimeNumberTheorem
