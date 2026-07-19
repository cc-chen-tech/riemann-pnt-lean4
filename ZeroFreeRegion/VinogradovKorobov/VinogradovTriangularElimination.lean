import ZeroFreeRegion.VinogradovKorobov.VinogradovBinomialMatrix

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- An integer matrix has the binomial leading coefficients required by
Wooley's translated congruence elimination. -/
def IsVinogradovBinomialCoefficientMatrix
    (p k r : ℕ) (Ω : Matrix (Fin r) (Fin r) ℤ) : Prop :=
  ∀ i j,
    Ω i j ≡ (Nat.choose (vinogradovBinomialPoint k r i) (j.val + 1) : ℤ)
      [ZMOD (p : ℤ)]

/-- The homogeneous integer congruence system represented by `Ω` modulo
`p^N`. -/
def IsVinogradovHomogeneousCongruenceSystem
    (p N r : ℕ) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (d : Fin r → ℤ) : Prop :=
  ∀ i, (∑ j, Ω i j * d j) ≡ 0 [ZMOD (p : ℤ) ^ N]

/-- Casting an integer homogeneous congruence system to `ZMod (p^N)` gives
the corresponding matrix equation. -/
theorem intMatrix_mulVec_eq_zero_of_homogeneousCongruenceSystem
    (p N r : ℕ) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (d : Fin r → ℤ)
    (h : IsVinogradovHomogeneousCongruenceSystem p N r Ω d) :
    (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N)))).mulVec
        (fun j ↦ (d j : ZMod (p ^ N))) = 0 := by
  funext i
  have hi := (ZMod.intCast_eq_intCast_iff
    (∑ j, Ω i j * d j) 0 (p ^ N)).mpr (h i)
  simpa only [Matrix.mulVec, dotProduct, Matrix.of_apply, Int.cast_sum,
    Int.cast_mul, Int.cast_zero, Pi.zero_apply] using hi

/-- Generic integer-matrix elimination modulo `p^N`: unit determinant of
the cast matrix makes every homogeneous solution component vanish. -/
theorem intMatrix_homogeneous_elimination_of_isUnit_det
    (p N r : ℕ) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hdet : IsUnit
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N)))).det)
    (d : Fin r → ℤ)
    (hd : IsVinogradovHomogeneousCongruenceSystem p N r Ω d) :
    ∀ j, d j ≡ 0 [ZMOD (p : ℤ) ^ N] := by
  let A : Matrix (Fin r) (Fin r) (ZMod (p ^ N)) :=
    Matrix.of fun i j ↦ (Ω i j : ZMod (p ^ N))
  let z : Fin r → ZMod (p ^ N) := fun j ↦ (d j : ZMod (p ^ N))
  have hAz : A.mulVec z = 0 :=
    intMatrix_mulVec_eq_zero_of_homogeneousCongruenceSystem p N r Ω d hd
  have hinjective : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_of_isUnit (A.isUnit_iff_isUnit_det.mpr hdet)
  have hzero : A.mulVec (0 : Fin r → ZMod (p ^ N)) = 0 := by simp
  have hz : z = 0 := hinjective (hAz.trans hzero.symm)
  intro j
  exact (ZMod.intCast_eq_intCast_iff (d j) 0 (p ^ N)).mp
    (by simpa only [z, Pi.zero_apply, Int.cast_zero] using congrFun hz j)

/-- The prime-power binomial coefficient system is injective: if its
integer linear combinations vanish modulo `p^N`, every component vanishes
modulo `p^N`.  This is the formal strong-congruence elimination step. -/
theorem vinogradovBinomial_homogeneous_elimination
    (p k r N : ℕ) [Fact p.Prime] (hrk : r ≤ k) (hkp : k < p)
    (hN : 0 < N) (Ω : Matrix (Fin r) (Fin r) ℤ)
    (hΩ : IsVinogradovBinomialCoefficientMatrix p k r Ω)
    (d : Fin r → ℤ)
    (hd : IsVinogradovHomogeneousCongruenceSystem p N r Ω d) :
    ∀ j, d j ≡ 0 [ZMOD (p : ℤ) ^ N] := by
  have hdet : IsUnit
      (Matrix.of (fun i j ↦ (Ω i j : ZMod (p ^ N)))).det :=
    isUnit_det_intMatrix_of_vinogradovBinomial_modEq
      p k r N hrk hkp hN Ω hΩ
  exact intMatrix_homogeneous_elimination_of_isUnit_det
    p N r Ω hdet d hd

end

end ZeroFreeRegion.VinogradovKorobov
