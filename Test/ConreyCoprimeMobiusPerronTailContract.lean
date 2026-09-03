import HardyTheorem.ConreyCoprimeMobiusPerronTail

open Complex MeasureTheory Set
open scoped BigOperators Interval

-- A bound on the whole coprime inverse, not a separately bounded Euler factor.
example {d : ℕ} [NeZero d] {s : ℂ} (hs : 1 < s.re) :
    ‖(riemannZeta s * ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-s)))⁻¹‖ ≤
      s.re / (s.re - 1) := by
  exact HardyTheorem.norm_conreyCoprimeMobiusEulerInverse_le hs

-- Both absolute tails, with no hidden modulus factor or normalization.
example {d : ℕ} [NeZero d] (α : ℂ) {X u K : ℝ}
    (hX : 0 < X) (hu : 0 < u) (hα : 0 < α.re + u) (hK : 0 < K) :
    let f : ℝ → ℂ := fun t => (X : ℂ) ^ ((u : ℂ) + t * I) *
      (riemannZeta (1 + α + ((u : ℂ) + t * I)) *
        ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((u : ℂ) + t * I)))))⁻¹ *
      (1 / ((u : ℂ) + t * I) ^ 2)
    (∫ t in Ioi K, ‖f t‖) ≤ X ^ u * ((1 + α.re + u) / (α.re + u)) / K ∧
    (∫ t in Iic (-K), ‖f t‖) ≤ X ^ u * ((1 + α.re + u) / (α.re + u)) / K := by
  exact HardyTheorem.conrey_coprime_mobius_perron_tail_bound α hX hu hα hK

-- Exact finite sum, floor cutoff, complex shift and normalized finite line.
example {d : ℕ} [NeZero d] (α : ℂ) {X u K : ℝ}
    (hX : 0 < X) (hu : 0 < u) (hα : 0 < α.re + u) (hK : 0 < K) :
    ‖(∑ n ∈ Finset.Icc 1 ⌊X⌋₊,
        (if n.Coprime d then (ArithmeticFunction.moebius n : ℂ) else 0) *
          (n : ℂ) ^ (-(1 + α)) * (Real.log (X / (n : ℝ)) : ℂ)) -
      (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-K)..K, (X : ℂ) ^ ((u : ℂ) + t * I) *
          (riemannZeta (1 + α + ((u : ℂ) + t * I)) *
            ∏ p ∈ d.primeFactors, (1 - (p : ℂ) ^ (-(1 + α + ((u : ℂ) + t * I)))))⁻¹ *
          (1 / ((u : ℂ) + t * I) ^ 2))‖ ≤
        X ^ u * ((1 + α.re + u) / (α.re + u)) / (Real.pi * K) := by
  exact HardyTheorem.conrey_coprime_mobius_log_perron_truncated α hX hu hα hK

#print axioms HardyTheorem.norm_conreyCoprimeMobiusEulerInverse_le
#print axioms HardyTheorem.conrey_coprime_mobius_perron_tail_bound
#print axioms HardyTheorem.conrey_coprime_mobius_log_perron_truncated
