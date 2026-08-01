import HardyTheorem.SelbergMollifiedTripleCollected
import HardyTheorem.SelbergSqrtZetaSignedPhasePolynomial

/-!
# Rational collection of the signed square-root-zeta phase polynomial

The real frequency of a signed triple `(m,d,l)` is
`log l - log m - log d`, hence depends only on the positive rational key
`l / (m*d)`.  Collecting by the normalized rational key exposes the exact
arithmetic fibers needed for Selberg's diagonal and gap estimates.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- The normalized positive rational key `l / (m*d)` of a signed triple. -/
noncomputable def selbergSqrtZetaSignedRationalKey
    (p : ℕ × (ℕ × ℕ)) : ℚ :=
  (p.2.2 : ℚ) / ((p.1 * p.2.1 : ℕ) : ℚ)

/-- The finite set of normalized rational keys in the signed support. -/
noncomputable def selbergSqrtZetaSignedRationalSupport
    (N X : ℕ) : Finset ℚ :=
  (selbergSqrtZetaSignedPhaseSupport N X).image
    selbergSqrtZetaSignedRationalKey

/-- The raw signed triples in one normalized rational frequency fiber. -/
noncomputable def selbergSqrtZetaSignedRationalFiber
    (N X : ℕ) (q : ℚ) : Finset (ℕ × (ℕ × ℕ)) :=
  (selbergSqrtZetaSignedPhaseSupport N X).filter
    (fun p => selbergSqrtZetaSignedRationalKey p = q)

/-- The signed square-root-zeta coefficient collected at a rational key. -/
noncomputable def selbergSqrtZetaSignedRationalCoeff
    (N X : ℕ) (q : ℚ) : ℂ :=
  ∑ p ∈ selbergSqrtZetaSignedRationalFiber N X q,
    selbergSqrtZetaSignedPhaseCoeff X p

/-- The real logarithmic frequency of a positive rational key. -/
noncomputable def selbergSqrtZetaSignedRationalFrequency
    (q : ℚ) : ℝ :=
  Real.log (q : ℝ)

/-- The signed triple polynomial indexed by normalized rational frequencies. -/
noncomputable def selbergSqrtZetaSignedRationalCollectedPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergSqrtZetaSignedRationalSupport N X)
    (selbergSqrtZetaSignedRationalCoeff N X)
    selbergSqrtZetaSignedRationalFrequency t

/-- Every rational key occurring in the signed support is positive. -/
theorem selbergSqrtZetaSignedRationalKey_pos_of_mem
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    0 < selbergSqrtZetaSignedRationalKey p := by
  simpa only [selbergSqrtZetaSignedRationalKey,
    selbergSqrtZetaSignedPhaseSupport,
    selbergMollifiedTripleKey,
    selbergMollifiedTripleSupport] using
    (selbergMollifiedTripleKey_pos_of_mem
      (N := N) (X := X) (p := p) hp)

/-- On the positive support, the signed real frequency is the logarithm of
the normalized rational key. -/
theorem selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key
    {N X : ℕ} {p : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaSignedPhaseFrequency p =
      selbergSqrtZetaSignedRationalFrequency
        (selbergSqrtZetaSignedRationalKey p) := by
  simpa only [selbergSqrtZetaSignedPhaseFrequency,
    selbergSqrtZetaSignedRationalFrequency,
    selbergSqrtZetaSignedRationalKey,
    selbergSqrtZetaSignedPhaseSupport,
    selbergMollifiedTripleFrequency,
    selbergMollifiedTripleCollectedFrequency,
    selbergMollifiedTripleKey,
    selbergMollifiedTripleSupport] using
    (selbergMollifiedTripleFrequency_eq_collectedFrequency_key
      (N := N) (X := X) (p := p) hp)

/-- On the signed positive support, equal real frequencies are equivalent to
equal normalized rational keys. -/
theorem selbergSqrtZetaSignedPhaseFrequency_eq_iff_rationalKey_eq
    {N X : ℕ} {p q : ℕ × (ℕ × ℕ)}
    (hp : p ∈ selbergSqrtZetaSignedPhaseSupport N X)
    (hq : q ∈ selbergSqrtZetaSignedPhaseSupport N X) :
    selbergSqrtZetaSignedPhaseFrequency p =
        selbergSqrtZetaSignedPhaseFrequency q ↔
      selbergSqrtZetaSignedRationalKey p =
        selbergSqrtZetaSignedRationalKey q := by
  simpa only [selbergSqrtZetaSignedPhaseFrequency,
    selbergSqrtZetaSignedRationalKey,
    selbergSqrtZetaSignedPhaseSupport,
    selbergMollifiedTripleFrequency,
    selbergMollifiedTripleKey,
    selbergMollifiedTripleSupport] using
    (selbergMollifiedTripleFrequency_eq_iff_key_eq
      (N := N) (X := X) (p := p) (q := q) hp hq)

/-- Collecting the signed triple expansion by normalized rational key
preserves the finite exponential polynomial exactly. -/
theorem selbergSqrtZetaSignedTriplePolynomial_eq_rationalCollectedPolynomial
    (N X : ℕ) (t : ℝ) :
    selbergSqrtZetaSignedTriplePolynomial N X t =
      selbergSqrtZetaSignedRationalCollectedPolynomial N X t := by
  classical
  let P := selbergSqrtZetaSignedPhaseSupport N X
  let K := selbergSqrtZetaSignedRationalSupport N X
  let g := selbergSqrtZetaSignedRationalKey
  let f : ℕ × (ℕ × ℕ) → ℂ := fun p =>
    selbergSqrtZetaSignedPhaseCoeff X p *
      Complex.exp (I * (selbergSqrtZetaSignedPhaseFrequency p * t))
  have hmaps : ∀ p ∈ P, g p ∈ K := by
    intro p hp
    exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
  have hfiber :
      (∑ p ∈ P, f p) =
        ∑ q ∈ K, ∑ p ∈ P.filter (fun p => g p = q), f p := by
    symm
    exact Finset.sum_fiberwise_of_maps_to hmaps f
  unfold selbergSqrtZetaSignedTriplePolynomial
    selbergSqrtZetaSignedRationalCollectedPolynomial
    MathlibAux.exponentialPolynomial
  calc
    (∑ p ∈ selbergSqrtZetaSignedPhaseSupport N X,
        selbergSqrtZetaSignedPhaseCoeff X p *
          Complex.exp
            (I * (selbergSqrtZetaSignedPhaseFrequency p * t))) =
        ∑ p ∈ P, f p := by rfl
    _ = ∑ q ∈ K, ∑ p ∈ P.filter (fun p => g p = q), f p := hfiber
    _ = ∑ q ∈ K,
        selbergSqrtZetaSignedRationalCoeff N X q *
          Complex.exp
            (I * (selbergSqrtZetaSignedRationalFrequency q * t)) := by
      apply Finset.sum_congr rfl
      intro q hq
      calc
        (∑ p ∈ P.filter (fun p => g p = q), f p) =
            ∑ p ∈ P.filter (fun p => g p = q),
              selbergSqrtZetaSignedPhaseCoeff X p *
                Complex.exp
                  (I * (selbergSqrtZetaSignedRationalFrequency q * t)) := by
          apply Finset.sum_congr rfl
          intro p hp
          have hpP : p ∈ selbergSqrtZetaSignedPhaseSupport N X := by
            simpa only [P] using (Finset.mem_filter.mp hp).1
          have hg : selbergSqrtZetaSignedRationalKey p = q := by
            simpa only [g] using (Finset.mem_filter.mp hp).2
          unfold f
          congr 2
          rw [selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hpP,
            hg]
        _ = (∑ p ∈ P.filter (fun p => g p = q),
              selbergSqrtZetaSignedPhaseCoeff X p) *
                Complex.exp
                  (I * (selbergSqrtZetaSignedRationalFrequency q * t)) := by
          rw [Finset.sum_mul]
        _ = selbergSqrtZetaSignedRationalCoeff N X q *
                Complex.exp
                  (I * (selbergSqrtZetaSignedRationalFrequency q * t)) := by
          congr 1

end HardyTheorem
