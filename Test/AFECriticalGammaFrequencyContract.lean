import HardyTheorem.AFECriticalGammaFrequency

open Complex HardyTheorem.AFE

-- This is the actual 2*pi*m Gamma term, not an abstract unit coefficient.
example (t : ℝ) {m : ℝ} (hm : 0 < m) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ‖((2 * Real.pi * m : ℝ) : ℂ) ^ (s - 1) *
      (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))‖ ≤
        m ^ (-(1 / 2) : ℝ) :=
  norm_criticalGammaFrequencyTerm_le t hm

-- One phase is chosen before K: independently chosen phases do not satisfy this contract.
example (t : ℝ) :
    let s : ℂ := (1 / 2 : ℂ) + I * t
    ∃ U : ℂ, ‖U‖ = 1 ∧ ∀ K : ℕ,
      ‖(∑ m ∈ Finset.Icc 1 K, ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) ^ (s - 1) *
        (Complex.exp (I * ((Real.pi / 2 : ℝ) : ℂ) * (1 - s)) * Complex.Gamma (1 - s))) -
          U * (∑ m ∈ Finset.Icc 1 K, (m : ℂ) ^ (s - 1))‖ ≤
        2 * Real.sqrt K * Real.exp (-2 * Real.pi * t) :=
  exists_unitPhase_criticalGammaFrequency_sums t

#print axioms norm_criticalGammaFrequencyTerm_le
#print axioms exists_unitPhase_criticalGammaFrequency_sums
