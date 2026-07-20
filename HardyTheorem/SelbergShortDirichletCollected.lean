import HardyTheorem.SelbergShortDirichletExpansion

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# The collected all-negative Selberg short Dirichlet polynomial

The uncollected expansion is indexed by triples `(m,n,l)`, but its frequency
depends only on the product `k = m*n*l`.  This file collects all triples with
the same product into one coefficient.  The resulting frequencies are
`-log k` on the explicit positive range `1 <= k <= N*X*X`, hence are pairwise
distinct.
-/

/-- The explicit positive product range supporting the collected polynomial. -/
noncomputable def selbergShortDirichletCollectedSupport
    (N X : ℕ) : Finset ℕ :=
  Finset.Icc 1 (N * X * X)

/-- The triples in the original finite support whose product is `k`. -/
noncomputable def selbergShortDirichletTriples
    (N X k : ℕ) : Finset (ℕ × (ℕ × ℕ)) :=
  (selbergShortDirichletTripleSupport N X).filter
    (fun p => p.1 * p.2.1 * p.2.2 = k)

/-- The coefficient obtained by collecting all triples with product `k`. -/
noncomputable def selbergShortDirichletCollectedCoeff
    (N X k : ℕ) : ℂ :=
  ∑ p ∈ selbergShortDirichletTriples N X k,
    selbergShortDirichletTripleCoeff X p

/-- The frequency attached to the collected product index `k`. -/
noncomputable def selbergShortDirichletCollectedFrequency
    (k : ℕ) : ℝ :=
  -Real.log (k : ℝ)

/-- The one-index exponential polynomial obtained after collecting equal
triple products. -/
noncomputable def selbergShortDirichletCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergShortDirichletCollectedSupport N X)
    (selbergShortDirichletCollectedCoeff N X)
    selbergShortDirichletCollectedFrequency t

@[simp] theorem selbergShortDirichletCollectedFrequency_eq_neg_log
    (k : ℕ) :
    selbergShortDirichletCollectedFrequency k = -Real.log (k : ℝ) := rfl

/-- Collecting the triple expansion by `k = m*n*l` preserves the finite
exponential polynomial exactly. -/
theorem selbergShortDirichletTriplePolynomial_eq_collectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergShortDirichletTriplePolynomial N X t =
      selbergShortDirichletCollectedPolynomial N X t := by
  classical
  let P := selbergShortDirichletTripleSupport N X
  let K := selbergShortDirichletCollectedSupport N X
  let g : ℕ × (ℕ × ℕ) → ℕ := fun p =>
    p.1 * p.2.1 * p.2.2
  let f : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergShortDirichletTripleCoeff X p *
      Complex.exp (I * (selbergShortDirichletTripleFrequency p * t))
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    rcases Finset.mem_product.mp (by simpa only [P,
        selbergShortDirichletTripleSupport] using hp) with ⟨hpN, hpXX⟩
    rcases Finset.mem_product.mp hpXX with ⟨hpnX, hplX⟩
    rcases Finset.mem_Icc.mp hpN with ⟨hm1, hmN⟩
    rcases Finset.mem_Icc.mp hpnX with ⟨hn1, hnX⟩
    rcases Finset.mem_Icc.mp hplX with ⟨hl1, hlX⟩
    exact Finset.mem_Icc.mpr
      ⟨Nat.mul_pos (Nat.mul_pos hm1 hn1) hl1,
        Nat.mul_le_mul (Nat.mul_le_mul hmN hnX) hlX⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ k ∈ K, ∑ p ∈ P.filter (fun p => g p = k), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergShortDirichletTriplePolynomial
  unfold selbergShortDirichletCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  calc
    (∑ p ∈ selbergShortDirichletTripleSupport N X,
        selbergShortDirichletTripleCoeff X p *
          Complex.exp (I * (selbergShortDirichletTripleFrequency p * t))) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ k ∈ K, ∑ p ∈ P.filter (fun p => g p = k), f p :=
      hfiber
    _ = ∑ k ∈ K,
        selbergShortDirichletCollectedCoeff N X k *
          Complex.exp (I * (selbergShortDirichletCollectedFrequency k * t)) := by
      apply Finset.sum_congr rfl
      intro k hk
      calc
        (∑ p ∈ P.filter (fun p => g p = k), f p) =
            ∑ p ∈ P.filter (fun p => g p = k),
              selbergShortDirichletTripleCoeff X p *
                Complex.exp
                  (I * (selbergShortDirichletCollectedFrequency k * t)) := by
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
              selbergShortDirichletTripleCoeff X p) *
                Complex.exp
                  (I * (selbergShortDirichletCollectedFrequency k * t)) := by
          rw [Finset.sum_mul]
        _ = selbergShortDirichletCollectedCoeff N X k *
                Complex.exp
                  (I * (selbergShortDirichletCollectedFrequency k * t)) := by
          congr 1

/-- On the explicit positive support, distinct product indices have distinct
negative-log frequencies. -/
theorem selbergShortDirichletCollectedFrequency_injective_on_support
    {N X j k : ℕ}
    (hj : j ∈ selbergShortDirichletCollectedSupport N X)
    (hk : k ∈ selbergShortDirichletCollectedSupport N X)
    (hfreq : selbergShortDirichletCollectedFrequency j =
      selbergShortDirichletCollectedFrequency k) :
    j = k := by
  have hjpos : (0 : ℝ) < j := by
    exact_mod_cast (Finset.mem_Icc.mp hj).1
  have hkpos : (0 : ℝ) < k := by
    exact_mod_cast (Finset.mem_Icc.mp hk).1
  have hlog : Real.log (j : ℝ) = Real.log (k : ℝ) := by
    exact neg_injective hfreq
  exact_mod_cast Real.log_injOn_pos hjpos hkpos hlog

/-- If all three finite ranges contain `1`, the collected constant
coefficient is exactly one. -/
@[simp] theorem selbergShortDirichletCollectedCoeff_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    selbergShortDirichletCollectedCoeff N X 1 = 1 := by
  classical
  have htriples :
      selbergShortDirichletTriples N X 1 = {(1, (1, 1))} := by
    ext p
    rcases p with ⟨m, n, l⟩
    constructor
    · intro hp
      rcases Finset.mem_filter.mp hp with ⟨hpSupport, hprod⟩
      have hmn_l : m * n = 1 ∧ l = 1 := mul_eq_one.mp hprod
      have hm_n : m = 1 ∧ n = 1 := mul_eq_one.mp hmn_l.1
      simp only [Finset.mem_singleton]
      rw [hm_n.1, hm_n.2, hmn_l.2]
    · intro hp
      simp only [Finset.mem_singleton] at hp
      rcases Prod.mk.inj hp with ⟨hm, hp'⟩
      rcases Prod.mk.inj hp' with ⟨hn, hl⟩
      subst hm
      subst hn
      subst hl
      apply Finset.mem_filter.mpr
      constructor
      · exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨le_rfl, hN⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨le_rfl, hX⟩,
              Finset.mem_Icc.mpr ⟨le_rfl, hX⟩⟩⟩
      · norm_num
  rw [selbergShortDirichletCollectedCoeff, htriples]
  simp [selbergShortDirichletTripleCoeff]

/-- Removing the `k = 1` term is exactly subtraction of the constant one;
the remaining support is the explicit positive interval `1 < k <= N*X*X`. -/
theorem selbergShortDirichletCollectedPolynomial_sub_one_eq
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) (t : ℝ) :
    selbergShortDirichletCollectedPolynomial N X t - 1 =
      MathlibAux.exponentialPolynomial
        (Finset.Ioc 1 (N * X * X))
        (selbergShortDirichletCollectedCoeff N X)
        selbergShortDirichletCollectedFrequency t := by
  have hOneMem : 1 ∈ selbergShortDirichletCollectedSupport N X := by
    exact Finset.mem_Icc.mpr
      ⟨le_rfl, Nat.mul_pos (Nat.mul_pos hN hX) hX⟩
  have hconst :
      selbergShortDirichletCollectedCoeff N X 1 *
          Complex.exp
            (I * (selbergShortDirichletCollectedFrequency 1 * t)) = 1 := by
    rw [selbergShortDirichletCollectedCoeff_one hN hX]
    simp [selbergShortDirichletCollectedFrequency]
  unfold selbergShortDirichletCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  rw [← Finset.sum_erase_add _ _ hOneMem]
  rw [hconst]
  rw [selbergShortDirichletCollectedSupport, Finset.Icc_erase_left]
  ring

end HardyTheorem
