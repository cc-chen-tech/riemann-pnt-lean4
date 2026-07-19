import ZeroFreeRegion.VinogradovKorobov.VinogradovLinearLift

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- First Hensel uniqueness layer for the power-sum system.  If two affine
lifts of a nonsingular residue vector have the same power sums modulo `p^2`,
then their correction vectors agree modulo `p`. -/
theorem vinogradovPowerSumInt_affine_corrections_unique_mod_prime
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (x h h' : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p)))
    (hpower : ∀ j : Fin k,
      vinogradovPowerSumInt (fun i ↦ x i + (p : ℤ) * h i) j ≡
        vinogradovPowerSumInt (fun i ↦ x i + (p : ℤ) * h' i) j
          [ZMOD (p : ℤ) ^ 2]) :
    ∀ i : Fin k, h i ≡ h' i [ZMOD (p : ℤ)] := by
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  have hlinear : ∀ j : Fin k,
      (vinogradovPowerSumJacobian x).mulVec h j ≡
        (vinogradovPowerSumJacobian x).mulVec h' j [ZMOD (p : ℤ)] := by
    intro j
    have hleft := vinogradovPowerSumInt_affine_modEq_sq (p : ℤ) x h j
    have hright := vinogradovPowerSumInt_affine_modEq_sq (p : ℤ) x h' j
    have hsum := hleft.symm.trans ((hpower j).trans hright)
    have hmul :
        (p : ℤ) * (vinogradovPowerSumJacobian x).mulVec h j ≡
          (p : ℤ) * (vinogradovPowerSumJacobian x).mulVec h' j
            [ZMOD (p : ℤ) ^ 2] :=
      Int.ModEq.add_left_cancel'
        (vinogradovPowerSumInt x j) hsum
    apply Int.ModEq.mul_left_cancel' hp0
    simpa [pow_two] using hmul
  have hmatrix :
      (vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
          (fun i : Fin k ↦ (h i : ZMod p)) =
        (vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
          (fun i : Fin k ↦ (h' i : ZMod p)) := by
    funext j
    have hj :=
      (ZMod.intCast_eq_intCast_iff
        ((vinogradovPowerSumJacobian x).mulVec h j)
        ((vinogradovPowerSumJacobian x).mulVec h' j) p).mpr (hlinear j)
    simpa [vinogradovPowerSumJacobian, Matrix.mulVec, dotProduct] using hj
  obtain ⟨w, hw, hunique⟩ :=
    existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq p k hkp
      (fun i : Fin k ↦ (x i : ZMod p)) hx
      ((vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
        (fun i : Fin k ↦ (h i : ZMod p)))
  have hh : (fun i : Fin k ↦ (h i : ZMod p)) = w := hunique _ rfl
  have hh' : (fun i : Fin k ↦ (h' i : ZMod p)) = w := hunique _ hmatrix.symm
  intro i
  exact (ZMod.intCast_eq_intCast_iff (h i) (h' i) p).mp
    (congrFun (hh.trans hh'.symm) i)

/-- Every prescribed first-order change of the power sums has an affine
integer lift modulo `p^2` at a nonsingular residue vector. -/
theorem exists_vinogradovPowerSumInt_affine_lift_mod_prime_sq
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    ∃ h : Fin k → ℤ, ∀ j : Fin k,
      vinogradovPowerSumInt (fun i ↦ x i + (p : ℤ) * h i) j ≡
        vinogradovPowerSumInt x j + (p : ℤ) * b j [ZMOD (p : ℤ) ^ 2] := by
  obtain ⟨w, hw, _⟩ :=
    existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq p k hkp
      (fun i : Fin k ↦ (x i : ZMod p)) hx
      (fun j : Fin k ↦ (b j : ZMod p))
  choose h hh using fun i : Fin k ↦ ZMod.intCast_surjective (w i)
  refine ⟨h, fun j ↦ ?_⟩
  have hmatrix :
      (vinogradovPowerSumJacobian x).mulVec h j ≡ b j [ZMOD (p : ℤ)] := by
    apply (ZMod.intCast_eq_intCast_iff
      ((vinogradovPowerSumJacobian x).mulVec h j) (b j) p).mp
    have hwj := congrFun hw j
    simpa [vinogradovPowerSumJacobian, Matrix.mulVec, dotProduct, hh] using hwj
  have hmul :
      (p : ℤ) * (vinogradovPowerSumJacobian x).mulVec h j ≡
        (p : ℤ) * b j [ZMOD (p : ℤ) ^ 2] := by
    simpa [pow_two] using hmatrix.mul_left'
  exact (vinogradovPowerSumInt_affine_modEq_sq (p : ℤ) x h j).trans
    (hmul.add_left (vinogradovPowerSumInt x j))

/-- The first-order affine lift exists and is unique modulo `p`. -/
theorem exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_sq
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    ∃ h : Fin k → ℤ,
      (∀ j : Fin k,
        vinogradovPowerSumInt (fun i ↦ x i + (p : ℤ) * h i) j ≡
          vinogradovPowerSumInt x j + (p : ℤ) * b j [ZMOD (p : ℤ) ^ 2]) ∧
      ∀ h' : Fin k → ℤ,
        (∀ j : Fin k,
          vinogradovPowerSumInt (fun i ↦ x i + (p : ℤ) * h' i) j ≡
            vinogradovPowerSumInt x j + (p : ℤ) * b j [ZMOD (p : ℤ) ^ 2]) →
        ∀ i : Fin k, h' i ≡ h i [ZMOD (p : ℤ)] := by
  obtain ⟨h, hh⟩ :=
    exists_vinogradovPowerSumInt_affine_lift_mod_prime_sq p k hkp x b hx
  refine ⟨h, hh, fun h' hh' ↦ ?_⟩
  apply vinogradovPowerSumInt_affine_corrections_unique_mod_prime p k hkp x h' h hx
  intro j
  exact (hh' j).trans (hh j).symm

/-- Taylor expansion modulo `q * r` whenever `r` divides the affine scale
`q`.  This is the form used for one-step prime-power lifting. -/
theorem vinogradovPowerSumInt_affine_modEq_mul_of_dvd
    {k : ℕ} (q r : ℤ) (hrq : r ∣ q) (x h : Fin k → ℤ) (j : Fin k) :
    vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
      vinogradovPowerSumInt x j +
        q * (vinogradovPowerSumJacobian x).mulVec h j [ZMOD q * r] := by
  apply (vinogradovPowerSumInt_affine_modEq_sq q x h j).of_dvd
  obtain ⟨c, rfl⟩ := hrq
  exact ⟨c, by ring⟩

/-- Uniqueness of the correction at any nonzero scale `q` divisible by `p`.
Equal power sums modulo `q * p` force equal corrections modulo `p`. -/
theorem vinogradovPowerSumInt_affine_corrections_unique_mod_prime_at_scale
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (q : ℤ) (hq0 : q ≠ 0)
    (hpq : (p : ℤ) ∣ q) (x h h' : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p)))
    (hpower : ∀ j : Fin k,
      vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
        vinogradovPowerSumInt (fun i ↦ x i + q * h' i) j
          [ZMOD q * (p : ℤ)]) :
    ∀ i : Fin k, h i ≡ h' i [ZMOD (p : ℤ)] := by
  have hlinear : ∀ j : Fin k,
      (vinogradovPowerSumJacobian x).mulVec h j ≡
        (vinogradovPowerSumJacobian x).mulVec h' j [ZMOD (p : ℤ)] := by
    intro j
    have hleft :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd q (p : ℤ) hpq x h j
    have hright :=
      vinogradovPowerSumInt_affine_modEq_mul_of_dvd q (p : ℤ) hpq x h' j
    have hsum := hleft.symm.trans ((hpower j).trans hright)
    have hmul :
        q * (vinogradovPowerSumJacobian x).mulVec h j ≡
          q * (vinogradovPowerSumJacobian x).mulVec h' j
            [ZMOD q * (p : ℤ)] :=
      Int.ModEq.add_left_cancel' (vinogradovPowerSumInt x j) hsum
    exact Int.ModEq.mul_left_cancel' hq0 hmul
  have hmatrix :
      (vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
          (fun i : Fin k ↦ (h i : ZMod p)) =
        (vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
          (fun i : Fin k ↦ (h' i : ZMod p)) := by
    funext j
    have hj :=
      (ZMod.intCast_eq_intCast_iff
        ((vinogradovPowerSumJacobian x).mulVec h j)
        ((vinogradovPowerSumJacobian x).mulVec h' j) p).mpr (hlinear j)
    simpa [vinogradovPowerSumJacobian, Matrix.mulVec, dotProduct] using hj
  obtain ⟨w, hw, hunique⟩ :=
    existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq p k hkp
      (fun i : Fin k ↦ (x i : ZMod p)) hx
      ((vinogradovPowerSumJacobian (fun i : Fin k ↦ (x i : ZMod p))).mulVec
        (fun i : Fin k ↦ (h i : ZMod p)))
  have hh : (fun i : Fin k ↦ (h i : ZMod p)) = w := hunique _ rfl
  have hh' : (fun i : Fin k ↦ (h' i : ZMod p)) = w := hunique _ hmatrix.symm
  intro i
  exact (ZMod.intCast_eq_intCast_iff (h i) (h' i) p).mp
    (congrFun (hh.trans hh'.symm) i)

/-- At every nonzero scale `q` divisible by `p`, every first-order target has
an affine lift modulo `q * p`, unique modulo `p`. -/
theorem exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_at_scale
    (p k : ℕ) [Fact p.Prime] (hkp : k < p) (q : ℤ) (hq0 : q ≠ 0)
    (hpq : (p : ℤ) ∣ q) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    ∃ h : Fin k → ℤ,
      (∀ j : Fin k,
        vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
          vinogradovPowerSumInt x j + q * b j [ZMOD q * (p : ℤ)]) ∧
      ∀ h' : Fin k → ℤ,
        (∀ j : Fin k,
          vinogradovPowerSumInt (fun i ↦ x i + q * h' i) j ≡
            vinogradovPowerSumInt x j + q * b j [ZMOD q * (p : ℤ)]) →
        ∀ i : Fin k, h' i ≡ h i [ZMOD (p : ℤ)] := by
  obtain ⟨w, hw, _⟩ :=
    existsUnique_vinogradovPowerSumJacobian_zmod_mulVec_eq p k hkp
      (fun i : Fin k ↦ (x i : ZMod p)) hx
      (fun j : Fin k ↦ (b j : ZMod p))
  choose h hh using fun i : Fin k ↦ ZMod.intCast_surjective (w i)
  have hmatrix : ∀ j : Fin k,
      (vinogradovPowerSumJacobian x).mulVec h j ≡ b j [ZMOD (p : ℤ)] := by
    intro j
    apply (ZMod.intCast_eq_intCast_iff
      ((vinogradovPowerSumJacobian x).mulVec h j) (b j) p).mp
    have hwj := congrFun hw j
    simpa [vinogradovPowerSumJacobian, Matrix.mulVec, dotProduct, hh] using hwj
  have hlift : ∀ j : Fin k,
      vinogradovPowerSumInt (fun i ↦ x i + q * h i) j ≡
        vinogradovPowerSumInt x j + q * b j [ZMOD q * (p : ℤ)] := by
    intro j
    exact (vinogradovPowerSumInt_affine_modEq_mul_of_dvd
      q (p : ℤ) hpq x h j).trans
        ((hmatrix j).mul_left'.add_left (vinogradovPowerSumInt x j))
  refine ⟨h, hlift, fun h' hh' ↦ ?_⟩
  apply vinogradovPowerSumInt_affine_corrections_unique_mod_prime_at_scale
    p k hkp q hq0 hpq x h' h hx
  intro j
  exact (hh' j).trans (hlift j).symm

/-- Prime-power specialization of the scale lifting theorem: a nonsingular
base lifts from scale `p^(n+1)` to modulus `p^(n+2)`, uniquely modulo `p`. -/
theorem exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_pow_succ
    (p k n : ℕ) [Fact p.Prime] (hkp : k < p) (x b : Fin k → ℤ)
    (hx : Function.Injective (fun i : Fin k ↦ (x i : ZMod p))) :
    ∃ h : Fin k → ℤ,
      (∀ j : Fin k,
        vinogradovPowerSumInt
            (fun i ↦ x i + (p : ℤ) ^ (n + 1) * h i) j ≡
          vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
            [ZMOD (p : ℤ) ^ (n + 2)]) ∧
      ∀ h' : Fin k → ℤ,
        (∀ j : Fin k,
          vinogradovPowerSumInt
              (fun i ↦ x i + (p : ℤ) ^ (n + 1) * h' i) j ≡
            vinogradovPowerSumInt x j + (p : ℤ) ^ (n + 1) * b j
              [ZMOD (p : ℤ) ^ (n + 2)]) →
        ∀ i : Fin k, h' i ≡ h i [ZMOD (p : ℤ)] := by
  have hp0 : (p : ℤ) ≠ 0 := by
    exact_mod_cast (Fact.out : p.Prime).ne_zero
  simpa [pow_succ] using
    (exists_unique_mod_vinogradovPowerSumInt_affine_lift_mod_prime_at_scale
      p k hkp ((p : ℤ) ^ (n + 1)) (pow_ne_zero _ hp0)
        (dvd_pow_self (p : ℤ) (Nat.succ_ne_zero n)) x b hx)

end

end ZeroFreeRegion.VinogradovKorobov
