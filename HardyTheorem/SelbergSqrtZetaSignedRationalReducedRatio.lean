import HardyTheorem.SelbergSqrtZetaSignedRationalCoefficientEnergySharp

/-!
# Reduced-ratio parameterization for the signed Selberg model

The rational coefficient energy is supported on pairs `(k,l)` with positive
denominator `k`.  Its off-diagonal condition is the integer equation
`l * k' = l' * k`.  This file gives the direct arithmetic normalization of
that equation: both pairs are multiples of one common coprime numerator and
denominator.
-/

namespace HardyTheorem

/-- Two natural pairs with positive denominators have equal cross-products
exactly when they are positive-denominator scalar multiples of one common
coprime pair.

The statement includes the zero-numerator case: then the reduced pair is
`(0,1)`.  Thus consumers can rewrite the complete rational correlation without
splitting off zero frequencies. -/
theorem crossProduct_eq_iff_exists_coprime_scales
    {k l k' l' : ℕ} (hk : 0 < k) (hk' : 0 < k') :
    l * k' = l' * k ↔
      ∃ a b d e : ℕ,
        Nat.Coprime a b ∧ 0 < b ∧
          l = a * d ∧ k = b * d ∧
            l' = a * e ∧ k' = b * e := by
  constructor
  · intro hcross
    let d := Nat.gcd l k
    let a := l / d
    let b := k / d
    have hdPos : 0 < d := by
      exact Nat.gcd_pos_of_pos_right l hk
    have hdDvdL : d ∣ l := Nat.gcd_dvd_left l k
    have hdDvdK : d ∣ k := Nat.gcd_dvd_right l k
    have hab : Nat.Coprime a b := by
      exact Nat.coprime_div_gcd_div_gcd hdPos
    have hl : l = a * d := by
      simpa only [a, d, Nat.mul_comm] using
        (Nat.div_mul_cancel hdDvdL).symm
    have hkFactor : k = b * d := by
      simpa only [b, d, Nat.mul_comm] using
        (Nat.div_mul_cancel hdDvdK).symm
    have hbPos : 0 < b := by
      have hbNe : b ≠ 0 := by
        intro hb
        rw [hb, zero_mul] at hkFactor
        omega
      exact Nat.pos_of_ne_zero hbNe
    have hReduced : a * k' = l' * b := by
      apply Nat.eq_of_mul_eq_mul_right hdPos
      simpa only [hl, hkFactor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hcross
    have hbDvd : b ∣ k' := by
      apply hab.symm.dvd_of_dvd_mul_left
      rw [hReduced]
      exact dvd_mul_left b l'
    let e := k' / b
    have hk'Factor : k' = b * e := by
      exact (Nat.mul_div_cancel' hbDvd).symm
    have hl'Factor : l' = a * e := by
      apply Nat.eq_of_mul_eq_mul_right hbPos
      simpa only [hk'Factor, Nat.mul_assoc, Nat.mul_comm,
        Nat.mul_left_comm] using hReduced.symm
    exact ⟨a, b, d, e, hab, hbPos, hl, hkFactor, hl'Factor, hk'Factor⟩
  · rintro ⟨a, b, d, e, _hab, _hbPos, rfl, rfl, rfl, rfl⟩
    simp only [Nat.mul_comm, Nat.mul_left_comm]

end HardyTheorem
