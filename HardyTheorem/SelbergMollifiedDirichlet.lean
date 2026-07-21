import HardyTheorem.CriticalLineShortDirichlet
import HardyTheorem.SelbergMollifier

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Arithmetic expansion of the mollified critical-line polynomial

The finite Dirichlet polynomial in the first zeta approximation and Selberg's
finite Moebius mollifier multiply by Dirichlet convolution.  This file records
that identity entirely at the finite-sum level.  The collected coefficient at
`k` is real and is supported on products `k = m * n` with `m <= N`, `n <= X`.
-/

/-- The admissible factorizations `k = m * n` arising from the two finite
Dirichlet polynomials. -/
noncomputable def selbergMollifiedDirichletPairs
    (N X k : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 X)).filter
    (fun p => p.1 * p.2 = k)

/-- The real Dirichlet-convolution coefficient obtained after multiplying the
zeta polynomial of length `N` by the concrete Selberg Moebius mollifier of
length `X`. -/
noncomputable def selbergMollifiedDirichletCoeff
    (N X k : ℕ) : ℝ :=
  ∑ p ∈ selbergMollifiedDirichletPairs N X k,
    selbergMoebiusCoeff X p.2

/-- Before collecting equal products, multiplication gives an exact finite
double sum. -/
theorem criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_doubleSum
    (N X : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (m * n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) := by
  unfold selbergMoebiusMollifier selbergMollifier
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Complex.natCast_mul_natCast_cpow]
  simp only [one_div, mul_inv_rev]
  ring

private theorem selbergMoebius_doubleSum_eq_convolutionSum
    (N X : ℕ) (s : ℂ) :
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (m * n : ℂ) ^ s)) =
      ∑ k ∈ Finset.Icc 1 (N * X),
        (selbergMollifiedDirichletCoeff N X k : ℂ) *
          (1 / (k : ℂ) ^ s) := by
  classical
  let P := (Finset.Icc 1 N).product (Finset.Icc 1 X)
  let K := Finset.Icc 1 (N * X)
  let g : ℕ × ℕ → ℕ := fun p => p.1 * p.2
  let f : ℕ × ℕ → ℂ := fun p =>
    (selbergMoebiusCoeff X p.2 : ℂ) *
      (1 / (g p : ℂ) ^ s)
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    rcases Finset.mem_product.mp hp with ⟨hpN, hpX⟩
    rcases Finset.mem_Icc.mp hpN with ⟨hp1, hpN⟩
    rcases Finset.mem_Icc.mp hpX with ⟨hp2, hpX⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos hp1 hp2, Nat.mul_le_mul hpN hpX⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ k ∈ K, ∑ p ∈ P.filter (fun p => g p = k), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  calc
    (∑ m ∈ Finset.Icc 1 N, ∑ n ∈ Finset.Icc 1 X,
        (selbergMoebiusCoeff X n : ℂ) *
          (1 / (m * n : ℂ) ^ s)) = ∑ p ∈ P, f p := by
      dsimp only [P, f, g]
      symm
      simpa only [Nat.cast_mul] using
        (Finset.sum_product (Finset.Icc 1 N) (Finset.Icc 1 X)
          (fun p : ℕ × ℕ =>
            (selbergMoebiusCoeff X p.2 : ℂ) *
              (1 / (p.1 * p.2 : ℂ) ^ s)))
    _ = ∑ k ∈ K, ∑ p ∈ P.filter (fun p => g p = k), f p := hfiber
    _ = ∑ k ∈ K,
        (selbergMollifiedDirichletCoeff N X k : ℂ) *
          (1 / (k : ℂ) ^ s) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ p ∈ P.filter (fun p => g p = k), f p) =
            ∑ p ∈ P.filter (fun p => g p = k),
              (selbergMoebiusCoeff X p.2 : ℂ) *
                (1 / (k : ℂ) ^ s) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hgpk : g p = k := (Finset.mem_filter.mp hp).2
          simp only [f, hgpk]
        _ = (∑ p ∈ P.filter (fun p => g p = k),
              (selbergMoebiusCoeff X p.2 : ℂ)) *
                (1 / (k : ℂ) ^ s) := by
          rw [Finset.sum_mul]
        _ = (selbergMollifiedDirichletCoeff N X k : ℂ) *
                (1 / (k : ℂ) ^ s) := by
          congr 1
          simp only [selbergMollifiedDirichletCoeff,
            selbergMollifiedDirichletPairs, P, g]
          push_cast
          rfl

/-- Collecting the double sum by the product `k = m * n` gives a finite
Dirichlet polynomial with the real convolution coefficients above. -/
theorem criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_convolutionSum
    (N X : ℕ) (t : ℝ) :
    (∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergMoebiusMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ k ∈ Finset.Icc 1 (N * X),
        (selbergMollifiedDirichletCoeff N X k : ℂ) *
          (1 / (k : ℂ) ^ ((1 / 2 : ℂ) + I * t)) := by
  rw [criticalLineDirichletPolynomial_mul_selbergMoebiusMollifier_eq_doubleSum]
  exact selbergMoebius_doubleSum_eq_convolutionSum N X
    ((1 / 2 : ℂ) + I * t)

/-- The collected coefficient vanishes outside the product support
`1 <= k <= N * X`. -/
theorem selbergMollifiedDirichletCoeff_eq_zero_of_not_mem
    {N X k : ℕ} (hk : k ∉ Finset.Icc 1 (N * X)) :
    selbergMollifiedDirichletCoeff N X k = 0 := by
  classical
  unfold selbergMollifiedDirichletCoeff
  apply Finset.sum_eq_zero
  intro p hp
  rcases Finset.mem_filter.mp hp with ⟨hpProd, hpk⟩
  rcases Finset.mem_product.mp hpProd with ⟨hpN, hpX⟩
  apply False.elim
  apply hk
  rcases Finset.mem_Icc.mp hpN with ⟨hp1, hpN⟩
  rcases Finset.mem_Icc.mp hpX with ⟨hp2, hpX⟩
  rw [← hpk]
  exact Finset.mem_Icc.mpr
    ⟨Nat.mul_pos hp1 hp2, Nat.mul_le_mul hpN hpX⟩

/-- The absolute value of a collected real coefficient is at most the number
of multiplicative factorizations of its index.  This divisor-count bound is
the pointwise input used when estimating the coefficient energy of the
mollified polynomial. -/
theorem abs_selbergMollifiedDirichletCoeff_le_card_divisorsAntidiagonal
    {N X k : ℕ} (hX : 2 ≤ X) :
    |selbergMollifiedDirichletCoeff N X k| ≤
      (k.divisorsAntidiagonal.card : ℝ) := by
  classical
  let S := selbergMollifiedDirichletPairs N X k
  have hsubset : S ⊆ k.divisorsAntidiagonal := by
    intro p hp
    rcases Finset.mem_filter.mp hp with ⟨hpProd, hpk⟩
    rcases Finset.mem_product.mp hpProd with ⟨hpN, hpX⟩
    have hp1 : 1 ≤ p.1 := (Finset.mem_Icc.mp hpN).1
    have hp2 : 1 ≤ p.2 := (Finset.mem_Icc.mp hpX).1
    rw [Nat.mem_divisorsAntidiagonal]
    exact ⟨hpk, by
      rw [← hpk]
      exact Nat.mul_ne_zero (by omega) (by omega)⟩
  calc
    |selbergMollifiedDirichletCoeff N X k| =
        |∑ p ∈ S, selbergMoebiusCoeff X p.2| := rfl
    _ ≤ ∑ p ∈ S, |selbergMoebiusCoeff X p.2| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro p hp
      have hpProd := (Finset.mem_filter.mp hp).1
      have hpX := (Finset.mem_product.mp hpProd).2
      exact abs_selbergMoebiusCoeff_le_one hX
        (Finset.mem_Icc.mp hpX).1 (Finset.mem_Icc.mp hpX).2
    _ = (S.card : ℝ) := by simp
    _ ≤ (k.divisorsAntidiagonal.card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsubset

end HardyTheorem
