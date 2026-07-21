import HardyTheorem.SelbergMollifiedTripleCollected

open scoped BigOperators

namespace HardyTheorem

/-!
# The zero frequency of the sign-preserving Selberg polynomial

For `P_N M_X * conj(M_X)`, the constant frequency consists of triples
`(m,n,l)` with `l = m*n`.  This is the main term that replaces the isolated
unit coefficient used by the invalid all-negative-frequency route.
-/

/-- The admissible `(m,n)` pairs whose reflected mollifier index `m*n` still
lies in the mollifier support. -/
noncomputable def selbergMollifiedTripleConstantPairs
    (N X : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.Icc 1 N).product (Finset.Icc 1 X)).filter
    (fun p => p.1 * p.2 ≤ X)

/-- On the positive triple support, reduced ratio one is equivalent to the
exact product relation `l = m*n`. -/
theorem selbergMollifiedTripleKey_eq_one_iff
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergMollifiedTripleSupport N X) :
    selbergMollifiedTripleKey p = 1 ↔ p.2.2 = p.1 * p.2.1 := by
  rcases Finset.mem_product.mp hp with ⟨hm, hnl⟩
  rcases Finset.mem_product.mp hnl with ⟨hn, _hl⟩
  have hm0 : p.1 ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hm).1
  have hn0 : p.2.1 ≠ 0 := Nat.ne_of_gt (Finset.mem_Icc.mp hn).1
  have hprod0 : p.1 * p.2.1 ≠ 0 := mul_ne_zero hm0 hn0
  unfold selbergMollifiedTripleKey
  constructor
  · intro h
    have hq : (p.2.2 : ℚ) = ((p.1 * p.2.1 : ℕ) : ℚ) :=
      (div_eq_one_iff_eq (by exact_mod_cast hprod0)).mp h
    exact_mod_cast hq
  · intro h
    rw [h]
    exact div_self (by exact_mod_cast hprod0)

/-- The ratio-one fiber is exactly the image of the admissible constant
pairs under `(m,n) |-> (m,n,m*n)`. -/
theorem selbergMollifiedTripleFiber_one_eq_constantPairs_image
    (N X : ℕ) :
    selbergMollifiedTripleFiber N X 1 =
      (selbergMollifiedTripleConstantPairs N X).image
        (fun p => (p.1, (p.2, p.1 * p.2))) := by
  classical
  ext q
  rcases q with ⟨m, n, l⟩
  constructor
  · intro hq
    rcases Finset.mem_filter.mp hq with ⟨hsupport, hkey⟩
    rcases Finset.mem_product.mp hsupport with ⟨hm, hnl⟩
    rcases Finset.mem_product.mp hnl with ⟨hn, hl⟩
    have hlprod : l = m * n :=
      (selbergMollifiedTripleKey_eq_one_iff hsupport).mp hkey
    apply Finset.mem_image.mpr
    refine ⟨(m, n), ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Finset.mem_product.mpr ⟨hm, hn⟩,
          by simpa only [← hlprod] using (Finset.mem_Icc.mp hl).2⟩
    · simpa only [hlprod]
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
    rcases p with ⟨m', n'⟩
    rcases Finset.mem_filter.mp hp with ⟨hpair, hprodX⟩
    rcases Finset.mem_product.mp hpair with ⟨hm, hn⟩
    have hmn1 : 1 ≤ m' * n' :=
      Nat.mul_pos (Finset.mem_Icc.mp hm).1 (Finset.mem_Icc.mp hn).1
    rw [← hpq]
    apply Finset.mem_filter.mpr
    have hsupport : (m', (n', m' * n')) ∈
        selbergMollifiedTripleSupport N X :=
      Finset.mem_product.mpr
        ⟨hm, Finset.mem_product.mpr
          ⟨hn, Finset.mem_Icc.mpr ⟨hmn1, hprodX⟩⟩⟩
    exact ⟨hsupport,
      (selbergMollifiedTripleKey_eq_one_iff hsupport).2 rfl⟩

/-- The collected zero-frequency coefficient is the exact finite main-term
sum over the relation `l = m*n`. -/
theorem selbergMollifiedTripleCollectedCoeff_one_eq_constantPairs
    (N X : ℕ) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ∑ p ∈ selbergMollifiedTripleConstantPairs N X,
        selbergMollifiedTripleCoeff X (p.1, (p.2, p.1 * p.2)) := by
  classical
  unfold selbergMollifiedTripleCollectedCoeff
  rw [selbergMollifiedTripleFiber_one_eq_constantPairs_image]
  exact Finset.sum_image fun a _ha b _hb hab => by
    exact Prod.ext
      (congrArg (fun q : ℕ × (ℕ × ℕ) => q.1) hab)
      (congrArg (fun q : ℕ × (ℕ × ℕ) => q.2.1) hab)

/-- On a constant-frequency triple, the three square-root normalisations
collapse to the reciprocal product `1 / (m*n)`. -/
theorem selbergMollifiedTripleCoeff_constant_eq
    {X m n : ℕ} (hm : 0 < m) (hn : 0 < n) :
    selbergMollifiedTripleCoeff X (m, (n, m * n)) =
      ((selbergMoebiusCoeff X n * selbergMoebiusCoeff X (m * n) /
        (m * n : ℝ) : ℝ) : ℂ) := by
  have hmreal : (0 : ℝ) < m := by exact_mod_cast hm
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrtm : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.2 hmreal
  have hsqrtn : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnreal
  have hsqrtmul : Real.sqrt ((m * n : ℕ) : ℝ) =
      Real.sqrt (m : ℝ) * Real.sqrt (n : ℝ) := by
    rw [Nat.cast_mul, Real.sqrt_mul (by positivity)]
  have hmSq : Real.sqrt (m : ℝ) ^ 2 = (m : ℝ) :=
    Real.sq_sqrt hmreal.le
  have hnSq : Real.sqrt (n : ℝ) ^ 2 = (n : ℝ) :=
    Real.sq_sqrt hnreal.le
  have hden :
      (((Real.sqrt m : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt m * Real.sqrt n : ℝ) : ℂ)⁻¹) =
        (((m * n : ℕ) : ℝ) : ℂ)⁻¹ := by
    calc
      (((Real.sqrt m : ℝ) : ℂ)⁻¹ *
          ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
          (((Real.sqrt m * Real.sqrt n : ℝ) : ℂ)⁻¹) =
          ((((Real.sqrt m : ℝ) : ℂ) *
              ((Real.sqrt n : ℝ) : ℂ))⁻¹) *
            ((((Real.sqrt m : ℝ) : ℂ) *
              ((Real.sqrt n : ℝ) : ℂ))⁻¹) := by
            push_cast
            rw [mul_inv]
      _ = (((((Real.sqrt m : ℝ) : ℂ) *
              ((Real.sqrt n : ℝ) : ℂ)) *
            (((Real.sqrt m : ℝ) : ℂ) *
              ((Real.sqrt n : ℝ) : ℂ)))⁻¹) := by
            rw [mul_inv]
      _ = (((m * n : ℕ) : ℝ) : ℂ)⁻¹ := by
            congr 1
            push_cast
            rw [← pow_two, mul_pow, hmSq, hnSq, Nat.cast_mul]
  unfold selbergMollifiedTripleCoeff
  simp only
  rw [hsqrtmul]
  rw [show
      ((selbergMoebiusCoeff X n : ℂ) *
            (selbergMoebiusCoeff X (m * n) : ℂ) *
            ((Real.sqrt m : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt n : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt m * Real.sqrt n : ℝ) : ℂ)⁻¹) =
        ((selbergMoebiusCoeff X n : ℂ) *
          (selbergMoebiusCoeff X (m * n) : ℂ)) *
          ((((Real.sqrt m : ℝ) : ℂ)⁻¹ *
            ((Real.sqrt n : ℝ) : ℂ)⁻¹) *
            ((Real.sqrt m * Real.sqrt n : ℝ) : ℂ)⁻¹) by ring]
  rw [hden]
  push_cast
  rw [div_eq_mul_inv]

/-- The zero-frequency main coefficient is therefore an explicit real
double sum with denominator `m*n`. -/
theorem selbergMollifiedTripleCollectedCoeff_one_eq_real_sum
    (N X : ℕ) :
    selbergMollifiedTripleCollectedCoeff N X 1 =
      ((∑ p ∈ selbergMollifiedTripleConstantPairs N X,
          selbergMoebiusCoeff X p.2 *
            selbergMoebiusCoeff X (p.1 * p.2) /
              (p.1 * p.2 : ℝ) : ℝ) : ℂ) := by
  rw [selbergMollifiedTripleCollectedCoeff_one_eq_constantPairs]
  push_cast
  apply Finset.sum_congr rfl
  intro p hp
  have hpData := (Finset.mem_filter.mp hp).1
  have hm : 0 < p.1 := (Finset.mem_Icc.mp (Finset.mem_product.mp hpData).1).1
  have hn : 0 < p.2 := (Finset.mem_Icc.mp (Finset.mem_product.mp hpData).2).1
  simpa [div_eq_mul_inv, Nat.cast_mul] using
    (selbergMollifiedTripleCoeff_constant_eq (X := X) hm hn)

end HardyTheorem
