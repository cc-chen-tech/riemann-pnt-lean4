import HardyTheorem.SelbergMollifiedTripleDirichlet

open Complex
open scoped BigOperators

namespace HardyTheorem

/-!
# Collecting the sign-preserving Selberg triple polynomial

The frequency of the triple `(m,n,l)` depends on the positive rational ratio
`l / (m*n)`.  We use `ℚ` as the canonical reduced key, so triples which give
the same rational number are collected before applying mean-square estimates.
-/

/-- The canonical reduced positive rational ratio `l / (m*n)` attached to a
triple `(m,n,l)`.  Rational normalization handles all frequency collisions. -/
noncomputable def selbergMollifiedTripleKey
    (p : ℕ × (ℕ × ℕ)) : ℚ :=
  (p.2.2 : ℚ) / ((p.1 * p.2.1 : ℕ) : ℚ)

/-- The finite set of reduced rational frequencies occurring in the original
triple support. -/
noncomputable def selbergMollifiedTripleCollectedSupport
    (N X : ℕ) : Finset ℚ :=
  (selbergMollifiedTripleSupport N X).image selbergMollifiedTripleKey

/-- The triples in the original support with canonical ratio key `q`. -/
noncomputable def selbergMollifiedTripleFiber
    (N X : ℕ) (q : ℚ) : Finset (ℕ × (ℕ × ℕ)) :=
  (selbergMollifiedTripleSupport N X).filter
    (fun p => selbergMollifiedTripleKey p = q)

/-- The coefficient obtained by summing over every triple with reduced ratio
key `q`. -/
noncomputable def selbergMollifiedTripleCollectedCoeff
    (N X : ℕ) (q : ℚ) : ℂ :=
  ∑ p ∈ selbergMollifiedTripleFiber N X q,
    selbergMollifiedTripleCoeff X p

/-- The logarithmic frequency attached to a positive reduced rational key. -/
noncomputable def selbergMollifiedTripleCollectedFrequency
    (q : ℚ) : ℝ :=
  Real.log (q : ℝ)

/-- The sign-preserving Selberg triple polynomial after collecting all equal
reduced rational frequencies. -/
noncomputable def selbergMollifiedTripleCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergMollifiedTripleCollectedSupport N X)
    (selbergMollifiedTripleCollectedCoeff N X)
    selbergMollifiedTripleCollectedFrequency t

/-- Every key occurring in the positive triple support is positive. -/
theorem selbergMollifiedTripleKey_pos_of_mem
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergMollifiedTripleSupport N X) :
    0 < selbergMollifiedTripleKey p := by
  rcases Finset.mem_product.mp hp with ⟨hm, hnl⟩
  rcases Finset.mem_product.mp hnl with ⟨hn, hl⟩
  have hmpos : 0 < p.1 := (Finset.mem_Icc.mp hm).1
  have hnpos : 0 < p.2.1 := (Finset.mem_Icc.mp hn).1
  have hlpos : 0 < p.2.2 := (Finset.mem_Icc.mp hl).1
  unfold selbergMollifiedTripleKey
  positivity

/-- On the positive support, the original logarithmic frequency is exactly
the logarithm of the canonical reduced rational key. -/
theorem selbergMollifiedTripleFrequency_eq_collectedFrequency_key
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergMollifiedTripleSupport N X) :
    selbergMollifiedTripleFrequency p =
      selbergMollifiedTripleCollectedFrequency
        (selbergMollifiedTripleKey p) := by
  rcases Finset.mem_product.mp hp with ⟨hm, hnl⟩
  rcases Finset.mem_product.mp hnl with ⟨hn, hl⟩
  have hm0 : (p.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hm).1)
  have hn0 : (p.2.1 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hn).1)
  have hl0 : (p.2.2 : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Finset.mem_Icc.mp hl).1)
  unfold selbergMollifiedTripleFrequency
  unfold selbergMollifiedTripleCollectedFrequency
  unfold selbergMollifiedTripleKey
  push_cast
  rw [Real.log_div hl0 (mul_ne_zero hm0 hn0), Real.log_mul hm0 hn0]
  ring

/-- Equal canonical keys give equal frequencies on the positive support. -/
theorem selbergMollifiedTripleKey_eq_imp_frequency_eq
    {N X : ℕ} {p q : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergMollifiedTripleSupport N X)
    (hq : q ∈ selbergMollifiedTripleSupport N X)
    (hkey : selbergMollifiedTripleKey p =
      selbergMollifiedTripleKey q) :
    selbergMollifiedTripleFrequency p =
      selbergMollifiedTripleFrequency q := by
  rw [selbergMollifiedTripleFrequency_eq_collectedFrequency_key hp,
    selbergMollifiedTripleFrequency_eq_collectedFrequency_key hq, hkey]

/-- On the positive support, frequency equality is equivalent to equality of
the canonical reduced rational keys. -/
theorem selbergMollifiedTripleFrequency_eq_iff_key_eq
    {N X : ℕ} {p q : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergMollifiedTripleSupport N X)
    (hq : q ∈ selbergMollifiedTripleSupport N X) :
    selbergMollifiedTripleFrequency p =
        selbergMollifiedTripleFrequency q ↔
      selbergMollifiedTripleKey p = selbergMollifiedTripleKey q := by
  constructor
  · intro hfreq
    have hlog :
        Real.log (selbergMollifiedTripleKey p : ℝ) =
          Real.log (selbergMollifiedTripleKey q : ℝ) := by
      change selbergMollifiedTripleCollectedFrequency
          (selbergMollifiedTripleKey p) =
        selbergMollifiedTripleCollectedFrequency
          (selbergMollifiedTripleKey q)
      rw [← selbergMollifiedTripleFrequency_eq_collectedFrequency_key hp,
        ← selbergMollifiedTripleFrequency_eq_collectedFrequency_key hq]
      exact hfreq
    have hpPos : (0 : ℝ) < (selbergMollifiedTripleKey p : ℚ) := by
      exact_mod_cast selbergMollifiedTripleKey_pos_of_mem hp
    have hqPos : (0 : ℝ) < (selbergMollifiedTripleKey q : ℚ) := by
      exact_mod_cast selbergMollifiedTripleKey_pos_of_mem hq
    have hcast : (selbergMollifiedTripleKey p : ℝ) =
        (selbergMollifiedTripleKey q : ℝ) :=
      Real.log_injOn_pos hpPos hqPos hlog
    exact_mod_cast hcast
  · exact selbergMollifiedTripleKey_eq_imp_frequency_eq hp hq

/-- Collecting the triple expansion by its reduced positive ratio preserves
the finite exponential polynomial exactly. -/
theorem selbergMollifiedTriplePolynomial_eq_collectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergMollifiedTriplePolynomial N X t =
      selbergMollifiedTripleCollectedPolynomial N X t := by
  classical
  let P := selbergMollifiedTripleSupport N X
  let K := selbergMollifiedTripleCollectedSupport N X
  let g := selbergMollifiedTripleKey
  let f : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergMollifiedTripleCoeff X p *
      Complex.exp (I * (selbergMollifiedTripleFrequency p * t))
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ q ∈ K, ∑ p ∈ P.filter (fun p => g p = q), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergMollifiedTriplePolynomial
  unfold selbergMollifiedTripleCollectedPolynomial
  unfold MathlibAux.exponentialPolynomial
  calc
    (∑ p ∈ selbergMollifiedTripleSupport N X,
        selbergMollifiedTripleCoeff X p *
          Complex.exp (I * (selbergMollifiedTripleFrequency p * t))) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ q ∈ K, ∑ p ∈ P.filter (fun p => g p = q), f p := hfiber
    _ = ∑ q ∈ K,
        selbergMollifiedTripleCollectedCoeff N X q *
          Complex.exp
            (I * (selbergMollifiedTripleCollectedFrequency q * t)) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        (∑ p ∈ P.filter (fun p => g p = q), f p) =
            ∑ p ∈ P.filter (fun p => g p = q),
              selbergMollifiedTripleCoeff X p *
                Complex.exp
                  (I * (selbergMollifiedTripleCollectedFrequency q * t)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpP : p ∈ selbergMollifiedTripleSupport N X := by
            simpa only [P] using (Finset.mem_filter.mp hp).1
          have hg : selbergMollifiedTripleKey p = q := by
            simpa only [g] using (Finset.mem_filter.mp hp).2
          unfold f
          congr 2
          rw [selbergMollifiedTripleFrequency_eq_collectedFrequency_key hpP,
            hg]
        _ = (∑ p ∈ P.filter (fun p => g p = q),
              selbergMollifiedTripleCoeff X p) *
                Complex.exp
                  (I * (selbergMollifiedTripleCollectedFrequency q * t)) := by
          rw [Finset.sum_mul]
        _ = selbergMollifiedTripleCollectedCoeff N X q *
                Complex.exp
                  (I * (selbergMollifiedTripleCollectedFrequency q * t)) := by
          congr 1

end HardyTheorem
