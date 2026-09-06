import HardyTheorem.SelbergJordanWeight
import HardyTheorem.SelbergSArithmeticPairBound

open Complex Nat Finset
open scoped BigOperators

namespace HardyTheorem

/-!
# The concrete Jordan quadratic identity in Selberg's diagonal sum

In Titchmarsh 10.11 the relevant gcd is
`gcd (kappa * nu) (lambda * mu)`.  Expanding its generalized Jordan
weight imposes the two conditions `rho | kappa * nu` and
`rho | lambda * mu`.  The resulting four finite sums factor as the square
of the exact pair sum already bounded in S19.
-/

/-- The gcd in Selberg's diagonal four-variable sum.  In the second pair
the variables are ordered `(mu, lambda)`; its product is of course
`lambda * mu`. -/
def selbergArithmeticDiagonalGcd
    {X : ℕ}
    (p q : selbergTaperIndex X × selbergTaperIndex X) : ℕ :=
  Nat.gcd (p.1.1 * p.2.1) (q.1.1 * q.2.1)

/-- The concrete finite version of Titchmarsh's `S(theta)`.  The first pair
is `(kappa, nu)` and the second is `(mu, lambda)`, so the two pair terms
have precisely the denominators
`kappa^(1-theta) * nu` and `mu^(1-theta) * lambda`. -/
noncomputable def selbergArithmeticDiagonalSum
    (X : ℕ) (theta : ℝ) : ℂ :=
  ∑ p : selbergTaperIndex X × selbergTaperIndex X,
    ∑ q : selbergTaperIndex X × selbergTaperIndex X,
      ((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
          (1 - theta) : ℝ) : ℂ) *
        selbergArithmeticPairTerm X theta p.1.1 p.2.1 *
        selbergArithmeticPairTerm X theta q.1.1 q.2.1

/-- The Jordan-weighted square obtained after expanding the diagonal gcd. -/
noncomputable def selbergArithmeticJordanQuadraticSum
    (X : ℕ) (theta : ℝ) : ℂ :=
  ∑ rho ∈ Finset.Icc 1 (X * X),
    (selbergJordanWeight (1 - theta) rho : ℂ) *
      selbergArithmeticPairSum rho X theta ^ 2

private theorem selberg_gcd_rpow_eq_sum_jordan_commonDivisors
    {X : ℕ} (theta : ℝ)
    (p q : selbergTaperIndex X × selbergTaperIndex X) :
    ((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
        (1 - theta) : ℝ) : ℂ) =
      ∑ rho ∈ Finset.Icc 1 (X * X),
        if rho ∣ p.1.1 * p.2.1 ∧ rho ∣ q.1.1 * q.2.1 then
          (selbergJordanWeight (1 - theta) rho : ℂ)
        else 0 := by
  classical
  let m : ℕ := p.1.1 * p.2.1
  let n : ℕ := q.1.1 * q.2.1
  have hmpos : 0 < m := Nat.mul_pos
    (Finset.mem_Icc.mp p.1.2).1 (Finset.mem_Icc.mp p.2.2).1
  have hnpos : 0 < n := Nat.mul_pos
    (Finset.mem_Icc.mp q.1.2).1 (Finset.mem_Icc.mp q.2.2).1
  have hmX : m ≤ X * X := Nat.mul_le_mul
    (Finset.mem_Icc.mp p.1.2).2 (Finset.mem_Icc.mp p.2.2).2
  have hgcdPos : 0 < Nat.gcd m n := Nat.gcd_pos_of_pos_left n hmpos
  have hset :
      (Finset.Icc 1 (X * X)).filter
          (fun rho => rho ∣ m ∧ rho ∣ n) =
        (Nat.gcd m n).divisors := by
    ext rho
    constructor
    · intro hrho
      rcases Finset.mem_filter.mp hrho with ⟨_hrhoIcc, hrhom, hrhon⟩
      exact Nat.mem_divisors.mpr
        ⟨Nat.dvd_gcd hrhom hrhon, Nat.ne_of_gt hgcdPos⟩
    · intro hrho
      rcases Nat.mem_divisors.mp hrho with ⟨hrhogcd, _hgcd0⟩
      have hrhom : rho ∣ m := hrhogcd.trans (Nat.gcd_dvd_left m n)
      have hrhon : rho ∣ n := hrhogcd.trans (Nat.gcd_dvd_right m n)
      have hrhopos : 0 < rho := Nat.pos_of_dvd_of_pos hrhogcd hgcdPos
      have hrhoX : rho ≤ X * X :=
        (Nat.le_of_dvd hmpos hrhom).trans hmX
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨hrhopos, hrhoX⟩, hrhom, hrhon⟩
  have hjordan := sum_divisors_selbergJordanWeight
    (1 - theta) (Nat.ne_of_gt hgcdPos)
  change ((((Nat.gcd m n : ℕ) : ℝ) ^ (1 - theta) : ℝ) : ℂ) = _
  rw [← hjordan]
  push_cast
  rw [← hset, Finset.sum_filter]

private theorem sum_common_divisor_kernel_eq_weighted_squares
    {P : Type*} [DecidableEq P]
    (I : Finset ℕ) (A : Finset P)
    (g : P → ℕ) (w : ℕ → ℂ) (b : P → ℂ) :
    (∑ p ∈ A, ∑ q ∈ A, ∑ rho ∈ I,
        if rho ∣ g p ∧ rho ∣ g q then w rho * b p * b q else 0) =
      ∑ rho ∈ I, w rho *
        (∑ p ∈ A.filter (fun p => rho ∣ g p), b p) ^ 2 := by
  classical
  calc
    (∑ p ∈ A, ∑ q ∈ A, ∑ rho ∈ I,
        if rho ∣ g p ∧ rho ∣ g q then w rho * b p * b q else 0) =
        ∑ rho ∈ I, ∑ p ∈ A, ∑ q ∈ A,
          if rho ∣ g p ∧ rho ∣ g q then w rho * b p * b q else 0 := by
      calc
        (∑ p ∈ A, ∑ q ∈ A, ∑ rho ∈ I,
            if rho ∣ g p ∧ rho ∣ g q then
              w rho * b p * b q else 0) =
            ∑ p ∈ A, ∑ rho ∈ I, ∑ q ∈ A,
              if rho ∣ g p ∧ rho ∣ g q then
                w rho * b p * b q else 0 := by
          apply Finset.sum_congr rfl
          intro p _hp
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = ∑ rho ∈ I,
        ∑ p ∈ A.filter (fun p => rho ∣ g p),
          ∑ q ∈ A.filter (fun q => rho ∣ g q),
            w rho * b p * b q := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro p _hp
      by_cases hpdiv : rho ∣ g p
      · simp only [hpdiv, true_and, if_true]
        rw [Finset.sum_filter]
      · simp [hpdiv]
    _ = ∑ rho ∈ I, w rho *
        (∑ p ∈ A.filter (fun p => rho ∣ g p), b p) ^ 2 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      calc
        (∑ p ∈ A.filter (fun p => rho ∣ g p),
            ∑ q ∈ A.filter (fun q => rho ∣ g q),
              w rho * b p * b q) =
            ∑ p ∈ A.filter (fun p => rho ∣ g p),
              (w rho * b p) *
                ∑ q ∈ A.filter (fun q => rho ∣ g q), b q := by
          apply Finset.sum_congr rfl
          intro p _hp
          rw [Finset.mul_sum]
        _ = (∑ p ∈ A.filter (fun p => rho ∣ g p),
              w rho * b p) *
              ∑ q ∈ A.filter (fun q => rho ∣ g q), b q := by
          rw [Finset.sum_mul]
        _ = w rho *
              (∑ p ∈ A.filter (fun p => rho ∣ g p), b p) *
              ∑ q ∈ A.filter (fun q => rho ∣ g q), b q := by
          congr 1
          rw [Finset.mul_sum]
        _ = w rho *
            (∑ p ∈ A.filter (fun p => rho ∣ g p), b p) ^ 2 := by
          rw [pow_two]
          ring

private theorem selbergArithmeticPairSum_eq_filtered_pair_sum
    (rho X : ℕ) (theta : ℝ) :
    selbergArithmeticPairSum rho X theta =
      ∑ p ∈ (Finset.univ :
          Finset (selbergTaperIndex X × selbergTaperIndex X)).filter
          (fun p => rho ∣ p.1.1 * p.2.1),
        selbergArithmeticPairTerm X theta p.1.1 p.2.1 := by
  classical
  unfold selbergArithmeticPairSum
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]

/-- S14: the concrete four-variable diagonal sum is exactly the generalized
Jordan-weighted square of the pair sums controlled by S19. -/
theorem selbergArithmeticDiagonalSum_eq_jordanQuadratic
    (X : ℕ) (theta : ℝ) :
    selbergArithmeticDiagonalSum X theta =
      selbergArithmeticJordanQuadraticSum X theta := by
  classical
  let P := (Finset.univ :
    Finset (selbergTaperIndex X × selbergTaperIndex X))
  let g : selbergTaperIndex X × selbergTaperIndex X → ℕ :=
    fun p => p.1.1 * p.2.1
  let b : selbergTaperIndex X × selbergTaperIndex X → ℂ :=
    fun p => selbergArithmeticPairTerm X theta p.1.1 p.2.1
  let w : ℕ → ℂ := fun rho =>
    (selbergJordanWeight (1 - theta) rho : ℂ)
  unfold selbergArithmeticDiagonalSum selbergArithmeticJordanQuadraticSum
  change (∑ p ∈ P, ∑ q ∈ P,
      ((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
          (1 - theta) : ℝ) : ℂ) * b p * b q) = _
  calc
    (∑ p ∈ P, ∑ q ∈ P,
        ((((selbergArithmeticDiagonalGcd p q : ℕ) : ℝ) ^
            (1 - theta) : ℝ) : ℂ) * b p * b q) =
        ∑ p ∈ P, ∑ q ∈ P, ∑ rho ∈ Finset.Icc 1 (X * X),
          if rho ∣ g p ∧ rho ∣ g q then w rho * b p * b q else 0 := by
      apply Finset.sum_congr rfl
      intro p _hp
      apply Finset.sum_congr rfl
      intro q _hq
      rw [selberg_gcd_rpow_eq_sum_jordan_commonDivisors theta p q]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro rho _hrho
      by_cases hdiv : rho ∣ g p ∧ rho ∣ g q
      · simp [g, w, hdiv]
      · simp [g, w, hdiv]
    _ = ∑ rho ∈ Finset.Icc 1 (X * X), w rho *
        (∑ p ∈ P.filter (fun p => rho ∣ g p), b p) ^ 2 :=
      sum_common_divisor_kernel_eq_weighted_squares
        (Finset.Icc 1 (X * X)) P g w b
    _ = ∑ rho ∈ Finset.Icc 1 (X * X),
        (selbergJordanWeight (1 - theta) rho : ℂ) *
          selbergArithmeticPairSum rho X theta ^ 2 := by
      apply Finset.sum_congr rfl
      intro rho _hrho
      dsimp [w]
      congr 1
      rw [selbergArithmeticPairSum_eq_filtered_pair_sum]

end HardyTheorem
