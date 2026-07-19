import MathlibAux.TimeDependentLogHilbert

open Complex MeasureTheory Set
open scoped BigOperators

#check MathlibAux.timeDependentLogPolynomial
#check MathlibAux.timeDependentNegLogPolynomial_eq_conj
#check MathlibAux.normSq_timeDependentLogPolynomial_eq
#check MathlibAux.hasDerivAt_timeDependentLogHilbertPrimitive
#check MathlibAux.norm_timeDependentLogHilbertPrimitive_le
#check MathlibAux.norm_timeDependentLogHilbertVariation_le
#check MathlibAux.norm_integral_timeDependentLogOffDiagonal_le

example (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) :
    Complex.normSq (MathlibAux.timeDependentLogPolynomial s coeff t) =
      (∑ n ∈ s, Complex.normSq (coeff t n)) +
        (MathlibAux.logOffDiagonalForm s (coeff t) (coeff t) t).re :=
  MathlibAux.normSq_timeDependentLogPolynomial_eq s coeff t

example (s : Finset ℕ) (coeff : ℝ → ℕ → ℂ) (t : ℝ) :
    MathlibAux.timeDependentNegLogPolynomial s coeff t =
      (starRingEnd ℂ)
        (MathlibAux.timeDependentLogPolynomial s
          (fun x n => (starRingEnd ℂ) (coeff x n)) t) :=
  MathlibAux.timeDependentNegLogPolynomial_eq_conj s coeff t

example (s : Finset ℕ) (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) {t : ℝ}
    (hderiv : ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t) :
    HasDerivAt (MathlibAux.timeDependentLogHilbertPrimitive s coeff)
      (I * MathlibAux.logOffDiagonalForm s (coeff t) (coeff t) t +
        MathlibAux.timeDependentLogHilbertVariation s coeff coeff' t) t :=
  MathlibAux.hasDerivAt_timeDependentLogHilbertPrimitive
    s coeff coeff' hpositive hderiv

example {N : ℕ} (hN : 0 < N) (s : Finset ℕ)
    (coeff coeff' : ℝ → ℕ → ℂ)
    (hpositive : ∀ n ∈ s, n ≠ 0) (hupper : ∀ n ∈ s, n ≤ N)
    {a b q E D : ℝ} (hab : a ≤ b) (hq : 0 < q)
    (hderiv : ∀ t ∈ Set.uIcc a b, ∀ n ∈ s,
      HasDerivAt (fun x ↦ coeff x n) (coeff' t n) t)
    (hoffInt : IntervalIntegrable
      (fun t => MathlibAux.logOffDiagonalForm s (coeff t) (coeff t) t)
      volume a b)
    (hvarInt : IntervalIntegrable
      (MathlibAux.timeDependentLogHilbertVariation s coeff coeff') volume a b)
    (henergy : ∀ t ∈ Set.uIcc a b,
      (∑ n ∈ s, Complex.normSq (coeff t n)) ≤ E)
    (hderivEnergy : ∀ t ∈ Set.uIcc a b,
      (∑ n ∈ s, Complex.normSq (coeff' t n)) ≤ D) :
    ‖∫ t in a..b,
        MathlibAux.logOffDiagonalForm s (coeff t) (coeff t) t‖ ≤
      4 * (5 * Real.pi + 4) * N * E +
        |b - a| *
          (2 * (5 * Real.pi + 4) * N *
            (q ^ 2 * D + (q ^ 2)⁻¹ * E)) :=
  MathlibAux.norm_integral_timeDependentLogOffDiagonal_le
    hN s coeff coeff' hpositive hupper hab hq hderiv hoffInt hvarInt
      henergy hderivEnergy

#print axioms MathlibAux.normSq_timeDependentLogPolynomial_eq
#print axioms MathlibAux.timeDependentNegLogPolynomial_eq_conj
#print axioms MathlibAux.hasDerivAt_timeDependentLogHilbertPrimitive
#print axioms MathlibAux.norm_timeDependentLogHilbertVariation_le
#print axioms MathlibAux.norm_integral_timeDependentLogOffDiagonal_le
