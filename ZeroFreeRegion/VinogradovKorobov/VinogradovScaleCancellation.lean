import ZeroFreeRegion.VinogradovKorobov.VinogradovTriangularElimination
import Mathlib.RingTheory.Coprime.Lemmas

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The residual modulus exponent `B'` in Wooley's far-scale branch. -/
def vinogradovFarScale (k r a b γ : ℕ) : ℕ :=
  (k - r + 1) * b - r * a - (k - r) * γ

/-- The column-aligned scale produced directly by the high-degree binomial
system.  Unlike `vinogradovFarScaleDifference`, the power of the center
depends on the degree. -/
def vinogradovAlignedFarScaleDifference
    (p k a γ : ℕ) (ω : ℤ) {r : ℕ} (d : Fin r → ℤ) (j : Fin r) : ℤ :=
  ω ^ (k - (j.val + 1)) *
    (p : ℤ) ^ (γ * (k - (j.val + 1)) + a * (j.val + 1)) * d j

/-- A factor coprime to `p` can be cancelled from a congruence modulo a
power of `p`. -/
theorem modEq_zero_cancel_coprime_primePower
    (p N q : ℕ) (ω d : ℤ)
    (hω : IsCoprime (p : ℤ) ω)
    (h : ω ^ q * d ≡ 0 [ZMOD (p : ℤ) ^ N]) :
    d ≡ 0 [ZMOD (p : ℤ) ^ N] := by
  rw [Int.modEq_zero_iff_dvd] at h ⊢
  exact hω.pow.dvd_of_dvd_mul_left h

/-- Cancelling an exact factor `p^e` lowers a prime-power modulus from
`p^M` to `p^(M-e)`. -/
theorem modEq_zero_cancel_primePower_scale
    (p e M : ℕ) (hp : p ≠ 0) (heM : e ≤ M) (d : ℤ)
    (h : (p : ℤ) ^ e * d ≡ 0 [ZMOD (p : ℤ) ^ M]) :
    d ≡ 0 [ZMOD (p : ℤ) ^ (M - e)] := by
  have hscaled :
      (p : ℤ) ^ e * d ≡ (p : ℤ) ^ e * 0
        [ZMOD (p : ℤ) ^ e * (p : ℤ) ^ (M - e)] := by
    simpa only [mul_zero, ← pow_add, Nat.add_sub_of_le heM] using h
  exact Int.ModEq.mul_left_cancel'
    (pow_ne_zero _ (Int.ofNat_ne_zero.mpr hp)) hscaled

/-- Cancelling both a `p`-coprime factor and an exact power of `p` leaves
the expected reduced prime-power modulus. -/
theorem modEq_zero_cancel_coprime_primePower_scale
    (p q e M : ℕ) (hp : p ≠ 0) (heM : e ≤ M)
    (ω d : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (h : ω ^ q * (p : ℤ) ^ e * d ≡ 0 [ZMOD (p : ℤ) ^ M]) :
    d ≡ 0 [ZMOD (p : ℤ) ^ (M - e)] := by
  have hscale :
      (p : ℤ) ^ e * (ω ^ q * d) ≡ 0 [ZMOD (p : ℤ) ^ M] := by
    simpa only [mul_assoc, mul_left_comm, mul_comm] using h
  have hcancel := modEq_zero_cancel_primePower_scale p e M hp heM
    (ω ^ q * d) hscale
  exact modEq_zero_cancel_coprime_primePower p (M - e) q ω d hω hcancel

/-- Uniform version of the scale cancellation in Wooley's equation (7.11).
The degree-dependent factors `p^(a(j+1))` are all weakened to the common
modulus obtained from the largest degree `r`. -/
theorem vinogradovScaledCongruences_to_uniform
    (p k r M a γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (d : Fin r → ℤ)
    (hd : ∀ j,
      ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (j.val + 1)) * d j ≡ 0
        [ZMOD (p : ℤ) ^ M]) :
    ∀ j, d j ≡ 0
      [ZMOD (p : ℤ) ^ (M - (γ * (k - r) + a * r))] := by
  intro j
  have hjr : j.val + 1 ≤ r := Nat.succ_le_iff.mpr j.isLt
  have hdegree :
      γ * (k - r) + a * (j.val + 1) ≤ γ * (k - r) + a * r :=
    Nat.add_le_add_left (Nat.mul_le_mul_left a hjr) _
  have hdegreeM : γ * (k - r) + a * (j.val + 1) ≤ M :=
    hdegree.trans hbudget
  have hj := modEq_zero_cancel_coprime_primePower_scale
    p (k - r) (γ * (k - r) + a * (j.val + 1)) M hp hdegreeM
      ω (d j) hω (hd j)
  exact hj.of_dvd (pow_dvd_pow (p : ℤ) (Nat.sub_le_sub_left hdegree M))

/-- Paper-facing form of the uniform cancellation theorem, with the ambient
modulus `(k-r+1)b` and residual exponent denoted by `B'`. -/
theorem vinogradovScaledCongruences_to_farScale
    (p k r a b γ : ℕ) (hp : p ≠ 0)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (d : Fin r → ℤ)
    (hd : ∀ j,
      ω ^ (k - r) *
          (p : ℤ) ^ (γ * (k - r) + a * (j.val + 1)) * d j ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)]) :
    ∀ j, d j ≡ 0 [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  have h := vinogradovScaledCongruences_to_uniform
    p k r ((k - r + 1) * b) a γ hp hbudget ω hω d hd
  simpa only [vinogradovFarScale, Nat.sub_sub, Nat.mul_comm,
    Nat.add_comm] using h

/-- Direct cancellation for the column-aligned high-degree system.  When
`γ ≤ a`, the largest `p`-adic scale occurs in degree `r`, so every component
survives modulo the same residual exponent `B'`. -/
theorem vinogradovAlignedCongruences_to_farScale
    (p k r a b γ : ℕ) (hp : p ≠ 0) (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω) (d : Fin r → ℤ)
    (hd : ∀ j,
      vinogradovAlignedFarScaleDifference p k a γ ω d j ≡ 0
        [ZMOD (p : ℤ) ^ ((k - r + 1) * b)]) :
    ∀ j, d j ≡ 0 [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  intro j
  let m := j.val + 1
  have hmr : m ≤ r := Nat.succ_le_iff.mpr j.isLt
  have hmk : m ≤ k := hmr.trans hrk
  have hk_split : k - m = (k - r) + (r - m) := by omega
  have hscale_le :
      γ * (k - m) + a * m ≤ γ * (k - r) + a * r := by
    calc
      γ * (k - m) + a * m =
          γ * (k - r) + γ * (r - m) + a * m := by
            rw [hk_split, Nat.mul_add]
      _ ≤ γ * (k - r) + a * (r - m) + a * m := by
            exact Nat.add_le_add_right
              (Nat.add_le_add_left (Nat.mul_le_mul_right (r - m) hγa) _) _
      _ = γ * (k - r) + a * r := by
            have har : a * (r - m) + a * m = a * r := by
              rw [← Nat.mul_add, Nat.sub_add_cancel hmr]
            rw [Nat.add_assoc, har]
  have hscale_budget :
      γ * (k - m) + a * m ≤ (k - r + 1) * b :=
    hscale_le.trans hbudget
  have hj := modEq_zero_cancel_coprime_primePower_scale
    p (k - m) (γ * (k - m) + a * m) ((k - r + 1) * b)
      hp hscale_budget ω (d j) hω (hd j)
  apply hj.of_dvd
  apply pow_dvd_pow (p : ℤ)
  simp only [vinogradovFarScale, Nat.sub_sub]
  simpa only [Nat.mul_comm, Nat.add_comm] using
    Nat.sub_le_sub_left hscale_le ((k - r + 1) * b)

end

end ZeroFreeRegion.VinogradovKorobov
