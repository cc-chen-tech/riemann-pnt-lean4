import HardyTheorem.SelbergSqrtZetaShortCollected

open Complex MeasureTheory
open scoped BigOperators

namespace HardyTheorem

/-!
# Finite square-root-zeta short Dirichlet expansion

This file identifies the finite product of the first zeta polynomial and two
copies of the tapered square-root-zeta mollifier with the triple exponential
polynomial whose collected coefficients were studied in
`SelbergSqrtZetaShortCollected`.
-/

/-- The finite tapered square-root-zeta mollifier as a Dirichlet polynomial. -/
noncomputable def selbergSqrtZetaMollifier
    (X : ℕ) (s : ℂ) : ℂ :=
  selbergMollifier X
    (fun n => (selbergSqrtZetaTaperedCoeff X n : ℂ)) s

/-- The explicit coefficient majorant for the square-root-zeta mollifier on
the critical line. -/
noncomputable def selbergSqrtZetaMollifierMajorant (X : ℕ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 X,
    |selbergSqrtZetaTaperedCoeff X n| * (Real.sqrt n)⁻¹

/-- The square-root-zeta mollifier is uniformly bounded in the height
parameter by its explicit coefficient majorant. -/
theorem norm_selbergSqrtZetaMollifier_criticalLine_le_majorant
    (X : ℕ) (t : ℝ) :
    ‖selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)‖ ≤
      selbergSqrtZetaMollifierMajorant X := by
  unfold selbergSqrtZetaMollifier selbergMollifier
  unfold selbergSqrtZetaMollifierMajorant
  calc
    ‖∑ n ∈ Finset.Icc 1 X,
        (selbergSqrtZetaTaperedCoeff X n : ℂ) *
          (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ ≤
        ∑ n ∈ Finset.Icc 1 X,
          ‖(selbergSqrtZetaTaperedCoeff X n : ℂ) *
            (1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t))‖ :=
      norm_sum_le _ _
    _ = ∑ n ∈ Finset.Icc 1 X,
        |selbergSqrtZetaTaperedCoeff X n| *
          (Real.sqrt n)⁻¹ := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnpos : 0 < n := by
        have hn1 := (Finset.mem_Icc.mp hn).1
        omega
      have hpow :
          ‖(n : ℂ) ^ ((1 / 2 : ℂ) + I * t)‖ = Real.sqrt n := by
        rw [Complex.norm_natCast_cpow_of_pos hnpos]
        simp [Real.sqrt_eq_rpow]
      rw [norm_mul, norm_div, norm_one, hpow, one_div]
      simp only [Complex.norm_real, Real.norm_eq_abs]

/-- The uncollected exponential polynomial indexed by `(m,d,l)`. -/
noncomputable def selbergSqrtZetaShortDirichletTriplePolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergShortDirichletTripleSupport N X)
    (selbergSqrtZetaShortDirichletTripleCoeff X)
    selbergShortDirichletTripleFrequency t

/-- Multiplication of the three finite factors gives the exact uncollected
triple sum. -/
theorem criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_tripleSum
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t) =
      ∑ m ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc 1 X,
        ∑ l ∈ Finset.Icc 1 X,
          (selbergSqrtZetaTaperedCoeff X d : ℂ) *
            (selbergSqrtZetaTaperedCoeff X l : ℂ) *
            (1 / ((m * d * l : ℕ) : ℂ) ^
              ((1 / 2 : ℂ) + I * t)) := by
  unfold selbergSqrtZetaMollifier selbergMollifier
  rw [Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro m hm
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  rw [← mul_assoc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l hl
  rw [show (((m * d * l : ℕ) : ℂ)) =
      (((m * d : ℕ) : ℂ) * (l : ℂ)) by norm_num,
    Complex.natCast_mul_natCast_cpow (m * d) l,
    show (((m * d : ℕ) : ℂ)) = (m : ℂ) * (d : ℂ) by norm_num,
    Complex.natCast_mul_natCast_cpow m d]
  simp only [one_div, mul_inv_rev]
  ring

private theorem inv_nat_cpow_half_eq_inv_sqrt_sqrtZeta
    (n : ℕ) :
    ((n : ℂ) ^ (1 / 2 : ℂ))⁻¹ =
      ((Real.sqrt n : ℝ) : ℂ)⁻¹ := by
  congr 1
  calc
    (n : ℂ) ^ (1 / 2 : ℂ) =
        (((n : ℝ) ^ (1 / 2 : ℝ) : ℝ) : ℂ) := by
      rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by norm_num]
      exact (Complex.ofReal_cpow
        (by positivity : (0 : ℝ) ≤ n) (1 / 2)).symm
    _ = ((Real.sqrt n : ℝ) : ℂ) := by
      rw [Real.sqrt_eq_rpow]

private theorem sqrtZetaShortTripleTerm_eq_exponentialTerm
    {X m d l : ℕ} (hm : m ≠ 0) (hd : d ≠ 0) (hl : l ≠ 0)
    (t : ℝ) :
    (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / ((m * d * l : ℕ) : ℂ) ^
            ((1 / 2 : ℂ) + I * t)) =
      selbergSqrtZetaShortDirichletTripleCoeff X (m, d, l) *
        Complex.exp
          (I * (selbergShortDirichletTripleFrequency
            (m, d, l) * t)) := by
  have hprod : m * d * l ≠ 0 :=
    Nat.mul_ne_zero (Nat.mul_ne_zero hm hd) hl
  rw [inv_nat_cpow_criticalLine_eq_exp hprod t,
    inv_nat_cpow_half_eq_inv_sqrt_sqrtZeta]
  unfold selbergSqrtZetaShortDirichletTripleCoeff
  unfold selbergShortDirichletTripleFrequency
  rw [show
      (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (((Real.sqrt ((m * d * l : ℕ) : ℝ) : ℝ) : ℂ)⁻¹ *
            Complex.exp
              ((-I * (Real.log ((m * d * l : ℕ) : ℝ) : ℂ)) * t)) =
        ((selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          ((Real.sqrt ((m * d * l : ℕ) : ℝ) : ℝ) : ℂ)⁻¹) *
        Complex.exp
          ((-I * (Real.log ((m * d * l : ℕ) : ℝ) : ℂ)) * t) by ring]
  congr 2
  push_cast
  ring

/-- The finite product is exactly the uncollected exponential polynomial. -/
theorem criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial
    (N X : ℕ) (t : ℝ) :
    ((∑ m ∈ Finset.Icc 1 N,
        1 / (m : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)) *
        selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t) =
      selbergSqrtZetaShortDirichletTriplePolynomial N X t := by
  rw [criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_tripleSum]
  unfold selbergSqrtZetaShortDirichletTriplePolynomial
  unfold MathlibAux.exponentialPolynomial
  unfold selbergShortDirichletTripleSupport
  let A := Finset.Icc 1 N
  let B := Finset.Icc 1 X
  let F : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergSqrtZetaShortDirichletTripleCoeff X p *
      Complex.exp
        (I * (selbergShortDirichletTripleFrequency p * t))
  calc
    (∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B,
        (selbergSqrtZetaTaperedCoeff X d : ℂ) *
          (selbergSqrtZetaTaperedCoeff X l : ℂ) *
          (1 / ((m * d * l : ℕ) : ℂ) ^
            ((1 / 2 : ℂ) + I * t))) =
        ∑ m ∈ A, ∑ d ∈ B, ∑ l ∈ B, F (m, d, l) := by
      apply Finset.sum_congr rfl
      intro m hm
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro l hl
      exact sqrtZetaShortTripleTerm_eq_exponentialTerm
        (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hd).1)
        (Nat.ne_of_gt (Finset.mem_Icc.mp hl).1) t
    _ = ∑ m ∈ A, ∑ q ∈ B.product B, F (m, q) := by
      apply Finset.sum_congr rfl
      intro m _hm
      exact (Finset.sum_product B B
        (fun q => F (m, q))).symm
    _ = ∑ p ∈ A.product (B.product B), F p :=
      (Finset.sum_product A (B.product B) F).symm

/-- The first zeta approximation remains uniform after multiplying by two
copies of the square-root-zeta mollifier.  Its remainder is controlled by
the square of the explicit mollifier majorant. -/
theorem exists_selbergSqrtZetaMollifiedZetaFirstApprox :
    ∃ C T0 : ℝ, 0 ≤ C ∧ 1 ≤ T0 ∧
      ∀ X : ℕ, ∀ T t : ℝ,
        T0 ≤ T → t ∈ Set.Icc T (2 * T) →
          ∃ E : ℂ,
            (riemannZeta ((1 / 2 : ℂ) + I * t) *
                selbergSqrtZetaMollifier X
                  ((1 / 2 : ℂ) + I * t)) *
              selbergSqrtZetaMollifier X
                ((1 / 2 : ℂ) + I * t) =
                selbergSqrtZetaShortDirichletTriplePolynomial
                  (firstZetaApproximationCutoff T) X t + E ∧
            ‖E‖ ≤ C / Real.sqrt T *
              selbergSqrtZetaMollifierMajorant X ^ 2 := by
  obtain ⟨C, T0, hC, hT0, happ⟩ := criticalLineZetaFirstApprox
  refine ⟨C, T0, hC, hT0, ?_⟩
  intro X T t hT ht
  obtain ⟨R, hzeta, hR⟩ := happ T t hT ht
  let M : ℂ :=
    selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * t)
  refine ⟨(R * M) * M, ?_, ?_⟩
  · rw [hzeta]
    have hpoly :=
      criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial
        (firstZetaApproximationCutoff T) X t
    dsimp only [M]
    calc
      ((∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) + R) *
            selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t) *
          selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t) =
        ((∑ n ∈ Finset.Icc 1 (firstZetaApproximationCutoff T),
            1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * t)) *
            selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t) +
        (R * selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)) *
          selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t) := by ring
      _ = selbergSqrtZetaShortDirichletTriplePolynomial
            (firstZetaApproximationCutoff T) X t +
          (R * selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)) *
            selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t) := by rw [hpoly]
  · have hM :=
      norm_selbergSqrtZetaMollifier_criticalLine_le_majorant X t
    have hmajorant_nonneg :
        0 ≤ selbergSqrtZetaMollifierMajorant X := by
      unfold selbergSqrtZetaMollifierMajorant
      positivity
    dsimp only [M]
    rw [norm_mul, norm_mul]
    calc
      ‖R‖ *
            ‖selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)‖ *
          ‖selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t)‖ ≤
        (C / Real.sqrt T) *
            ‖selbergSqrtZetaMollifier X
              ((1 / 2 : ℂ) + I * t)‖ *
          ‖selbergSqrtZetaMollifier X
            ((1 / 2 : ℂ) + I * t)‖ := by
          gcongr
      _ ≤ (C / Real.sqrt T) *
          selbergSqrtZetaMollifierMajorant X *
            selbergSqrtZetaMollifierMajorant X := by
          gcongr
      _ = C / Real.sqrt T *
          selbergSqrtZetaMollifierMajorant X ^ 2 := by ring

/-- The one-index polynomial obtained after collecting equal triple
products. -/
noncomputable def selbergSqrtZetaShortDirichletCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergShortDirichletCollectedSupport N X)
    (selbergSqrtZetaShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency t

/-- Collecting equal product frequencies preserves the finite polynomial. -/
theorem selbergSqrtZetaShortDirichletTriplePolynomial_eq_collectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaShortDirichletTriplePolynomial N X t =
      selbergSqrtZetaShortDirichletCollectedPolynomial N X t := by
  classical
  let P := selbergShortDirichletTripleSupport N X
  let K := selbergShortDirichletCollectedSupport N X
  let g : ℕ × (ℕ × ℕ) → ℕ := fun p =>
    p.1 * p.2.1 * p.2.2
  let f : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergSqrtZetaShortDirichletTripleCoeff X p *
      Complex.exp
        (I * (selbergShortDirichletTripleFrequency p * t))
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    rcases Finset.mem_product.mp (by simpa only [P,
        selbergShortDirichletTripleSupport] using hp) with
      ⟨hpN, hpXX⟩
    rcases Finset.mem_product.mp hpXX with ⟨hpdX, hplX⟩
    rcases Finset.mem_Icc.mp hpN with ⟨hm1, hmN⟩
    rcases Finset.mem_Icc.mp hpdX with ⟨hd1, hdX⟩
    rcases Finset.mem_Icc.mp hplX with ⟨hl1, hlX⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Nat.mul_pos hm1 hd1) hl1,
        Nat.mul_le_mul (Nat.mul_le_mul hmN hdX) hlX⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ k ∈ K, ∑ p ∈ P.filter (fun p => g p = k), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergSqrtZetaShortDirichletTriplePolynomial
  unfold selbergSqrtZetaShortDirichletCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  calc
    (∑ p ∈ selbergShortDirichletTripleSupport N X,
        selbergSqrtZetaShortDirichletTripleCoeff X p *
          Complex.exp
            (I * (selbergShortDirichletTripleFrequency p * t))) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ k ∈ K,
        ∑ p ∈ P.filter (fun p => g p = k), f p := hfiber
    _ = ∑ k ∈ K,
        selbergSqrtZetaShortDirichletCollectedCoeff N X k *
          Complex.exp
            (I * (selbergShortDirichletCollectedFrequency k * t)) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ p ∈ P.filter (fun p => g p = k), f p) =
            ∑ p ∈ P.filter (fun p => g p = k),
              selbergSqrtZetaShortDirichletTripleCoeff X p *
                Complex.exp
                  (I *
                    (selbergShortDirichletCollectedFrequency k * t)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hgpk : g p = k := (Finset.mem_filter.mp hp).2
          unfold f
          congr 2
          unfold selbergShortDirichletTripleFrequency
          unfold selbergShortDirichletCollectedFrequency
          change p.1 * p.2.1 * p.2.2 = k at hgpk
          rw [hgpk]
        _ = (∑ p ∈ P.filter (fun p => g p = k),
              selbergSqrtZetaShortDirichletTripleCoeff X p) *
                Complex.exp
                  (I *
                    (selbergShortDirichletCollectedFrequency k * t)) := by
          rw [Finset.sum_mul]
        _ = selbergSqrtZetaShortDirichletCollectedCoeff N X k *
                Complex.exp
                  (I *
                    (selbergShortDirichletCollectedFrequency k * t)) := by
          congr 1

/-- The collected constant coefficient is one. -/
@[simp] theorem selbergSqrtZetaShortDirichletCollectedCoeff_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergSqrtZetaShortDirichletCollectedCoeff N X 1 = 1 := by
  classical
  have htriples :
      selbergShortDirichletTriples N X 1 = {(1, (1, 1))} := by
    ext p
    rcases p with ⟨m, d, l⟩
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨_hpSupport, hprod⟩
      have hmd_l : m * d = 1 ∧ l = 1 := mul_eq_one.mp hprod
      have hm_d : m = 1 ∧ d = 1 := mul_eq_one.mp hmd_l.1
      simp only [Finset.mem_singleton]
      rw [hm_d.1, hm_d.2, hmd_l.2]
    · intro hp
      simp only [Finset.mem_singleton] at hp
      rcases Prod.mk.inj hp with ⟨hm, hp'⟩
      rcases Prod.mk.inj hp' with ⟨hd, hl⟩
      subst hm
      subst hd
      subst hl
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr
          ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩,
            Finset.mem_product.mpr
              ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX⟩,
                Finset.mem_Icc.mpr ⟨le_rfl, hX⟩⟩⟩
      · norm_num
  rw [selbergSqrtZetaShortDirichletCollectedCoeff, htriples]
  simp [selbergSqrtZetaShortDirichletTripleCoeff]

/-- Removing the constant term leaves exactly the positive nonconstant
product range. -/
theorem selbergSqrtZetaShortDirichletCollectedPolynomial_sub_one_eq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (t : ℝ) :
    selbergSqrtZetaShortDirichletCollectedPolynomial N X t - 1 =
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency t := by
  have hOneMem :
      1 ∈ selbergShortDirichletCollectedSupport N X := by
    exact Finset.mem_Icc.mpr
      ⟨le_rfl, Nat.mul_pos (Nat.mul_pos hN hX) hX⟩
  have hconst :
      selbergSqrtZetaShortDirichletCollectedCoeff N X 1 *
          Complex.exp
            (I * (selbergShortDirichletCollectedFrequency 1 * t)) =
        1 := by
    rw [selbergSqrtZetaShortDirichletCollectedCoeff_one hN hX]
    simp [selbergShortDirichletCollectedFrequency]
  unfold selbergSqrtZetaShortDirichletCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  rw [← Finset.sum_erase_add _ _ hOneMem, hconst,
    selbergShortDirichletCollectedSupport,
    Finset.Icc_erase_left]
  ring

/-- The finite short integral after subtracting its unit coefficient. -/
noncomputable def selbergSqrtZetaMollifiedShortDirichletPolynomial
    (H : ℝ) (N X : ℕ) (t : ℝ) : ℂ :=
  ∫ u in t..t + H,
    (((∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) *
      selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * u)) *
      selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * u) - 1)

/-- The short integral is exactly the sliding collected exponential
polynomial. -/
theorem selbergSqrtZetaMollifiedShortDirichletPolynomial_eq_slidingCollected
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (H t : ℝ) :
    selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t =
      MathlibAux.slidingExponentialPolynomialIntegral
        (Finset.Ioc 1 (N * X * X))
        (selbergSqrtZetaShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency H t := by
  unfold selbergSqrtZetaMollifiedShortDirichletPolynomial
  unfold MathlibAux.slidingExponentialPolynomialIntegral
  apply intervalIntegral.integral_congr
  intro u _hu
  change
    (((∑ n ∈ Finset.Icc 1 N,
        1 / (n : ℂ) ^ ((1 / 2 : ℂ) + I * u)) *
      selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * u)) *
      selbergSqrtZetaMollifier X ((1 / 2 : ℂ) + I * u) - 1) = _
  rw [criticalLineDirichletPolynomial_mul_sqrtZetaMollifier_sq_eq_exponentialPolynomial,
    selbergSqrtZetaShortDirichletTriplePolynomial_eq_collectedPolynomial,
    selbergSqrtZetaShortDirichletCollectedPolynomial_sub_one_eq
      hN hX]

/-- The start-variable second moment is bounded by the explicit
diagonal-plus-frequency-gap sum for the actual finite coefficients. -/
theorem integral_normSq_selbergSqrtZetaMollifiedShortDirichletPolynomial_le_gapSum
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) {A B H : ℝ} :
    (∫ t in A..B,
        Complex.normSq
          (selbergSqrtZetaMollifiedShortDirichletPolynomial
            H N X t)) ≤
      ∑ m ∈ Finset.Ioc 1 (N * X * X),
        ∑ n ∈ Finset.Ioc 1 (N * X * X),
          if m = n then
            (B - A) * Complex.normSq
              (MathlibAux.slidingExponentialCoefficient H
                (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                selbergShortDirichletCollectedFrequency n)
          else
            2 * ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency m‖ *
                ‖MathlibAux.slidingExponentialCoefficient H
                  (selbergSqrtZetaShortDirichletCollectedCoeff N X)
                  selbergShortDirichletCollectedFrequency n‖ /
              |selbergShortDirichletCollectedFrequency m -
                selbergShortDirichletCollectedFrequency n| := by
  rw [show (fun t : ℝ => Complex.normSq
      (selbergSqrtZetaMollifiedShortDirichletPolynomial H N X t)) =
      fun t : ℝ => Complex.normSq
        (MathlibAux.slidingExponentialPolynomialIntegral
          (Finset.Ioc 1 (N * X * X))
          (selbergSqrtZetaShortDirichletCollectedCoeff N X)
          selbergShortDirichletCollectedFrequency H t) by
    funext t
    rw [selbergSqrtZetaMollifiedShortDirichletPolynomial_eq_slidingCollected
      hN hX]]
  apply
    MathlibAux.integral_normSq_slidingExponentialPolynomialIntegral_le
  intro m hm n hn hmn hfreq
  apply hmn
  apply selbergShortDirichletCollectedFrequency_injective_on_support
    (N := N) (X := X)
  · exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ioc.mp hm).1.le,
        (Finset.mem_Ioc.mp hm).2⟩
  · exact Finset.mem_Icc.mpr
      ⟨(Finset.mem_Ioc.mp hn).1.le,
        (Finset.mem_Ioc.mp hn).2⟩
  · exact hfreq

end HardyTheorem
