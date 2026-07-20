import ZeroFreeRegion.VinogradovKorobov.VinogradovTranslatedCoefficientMatrix

open scoped Polynomial

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

/-- The first `r` nonconstant coefficients of an arbitrary integer
polynomial.  This isolates the low-degree system from the still-separate
high-degree Taylor tail. -/
def vinogradovLowDegreePart (r : ℕ)
    (P : Polynomial ℤ) : Polynomial ℤ :=
  ∑ j : Fin r,
    Polynomial.C (P.coeff (j.val + 1)) * Polynomial.X ^ (j.val + 1)

@[simp] theorem eval_vinogradovLowDegreePart
    (r : ℕ) (P : Polynomial ℤ) (z : ℤ) :
    (vinogradovLowDegreePart r P).eval z =
      ∑ j : Fin r, P.coeff (j.val + 1) * z ^ (j.val + 1) := by
  simp [vinogradovLowDegreePart, Polynomial.eval_finset_sum]

theorem coeff_vinogradovLowDegreePart_of_pos_le
    (r d : ℕ) (P : Polynomial ℤ) (hd0 : 0 < d) (hdr : d ≤ r) :
    (vinogradovLowDegreePart r P).coeff d = P.coeff d := by
  let j : Fin r := ⟨d - 1, by omega⟩
  rw [vinogradovLowDegreePart, Polynomial.finset_sum_coeff,
    Finset.sum_eq_single j]
  · simp [j, Nat.sub_add_cancel hd0]
  · intro i _ hij
    have hne : d ≠ i.val + 1 := by
      intro hi
      apply hij
      apply Fin.ext
      dsimp only [j]
      omega
    simp [hne]
  · simp

@[simp] theorem coeff_zero_vinogradovLowDegreePart
    (r : ℕ) (P : Polynomial ℤ) :
    (vinogradovLowDegreePart r P).coeff 0 = 0 := by
  simp [vinogradovLowDegreePart]

theorem coeff_vinogradovLowDegreePart_eq_zero_of_lt
    (r d : ℕ) (P : Polynomial ℤ) (hrd : r < d) :
    (vinogradovLowDegreePart r P).coeff d = 0 := by
  rw [vinogradovLowDegreePart, Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro j _
  have hne : d ≠ j.val + 1 := by omega
  simp [hne]

/-- Beyond the low-degree projection, polynomial dilation by `p^a` gives
every coefficient the uniform tail factor `p^(a(r+1))`. -/
theorem primePower_dvd_coeff_dilation_sub_lowDegreePart
    (p a r d : ℕ) (H : Polynomial ℤ) (hzero : H.coeff 0 = 0) :
    (p : ℤ) ^ (a * (r + 1)) ∣
      (vinogradovPolynomialDilation ((p : ℤ) ^ a) H -
        vinogradovLowDegreePart r
          (vinogradovPolynomialDilation ((p : ℤ) ^ a) H)).coeff d := by
  rw [Polynomial.coeff_sub]
  by_cases hd0 : d = 0
  · subst d
    simp only [coeff_zero_vinogradovLowDegreePart, sub_zero,
      vinogradovPolynomialDilation, Polynomial.comp_C_mul_X_coeff,
      hzero, pow_zero, mul_one]
    exact dvd_zero _
  by_cases hdr : d ≤ r
  · have hdpos : 0 < d := Nat.pos_of_ne_zero hd0
    rw [coeff_vinogradovLowDegreePart_of_pos_le r d _ hdpos hdr,
      sub_self]
    exact dvd_zero _
  · have hrd : r < d := Nat.lt_of_not_ge hdr
    rw [coeff_vinogradovLowDegreePart_eq_zero_of_lt r d _ hrd, sub_zero]
    simp only [vinogradovPolynomialDilation,
      Polynomial.comp_C_mul_X_coeff]
    rw [← pow_mul]
    exact dvd_mul_of_dvd_right
      (pow_dvd_pow (p : ℤ) (Nat.mul_le_mul_left a (Nat.succ_le_iff.mpr hrd))) _

/-- A polynomial with zero constant coefficient is its first `r`
nonconstant terms plus a tail starting in degree `r+1`. -/
theorem exists_eq_vinogradovLowDegreePart_add_tail
    (r : ℕ) (P : Polynomial ℤ) (hzero : P.coeff 0 = 0) :
    ∃ θ : Polynomial ℤ,
      P = vinogradovLowDegreePart r P + Polynomial.X ^ (r + 1) * θ := by
  have hdiv : Polynomial.X ^ (r + 1) ∣
      P - vinogradovLowDegreePart r P := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    rw [Polynomial.coeff_sub]
    by_cases hd0 : d = 0
    · subst d
      simp [hzero]
    · have hpos : 0 < d := Nat.pos_of_ne_zero hd0
      have hdr : d ≤ r := by omega
      rw [coeff_vinogradovLowDegreePart_of_pos_le r d P hpos hdr,
        sub_self]
  obtain ⟨θ, hθ⟩ := hdiv
  refine ⟨θ, ?_⟩
  rw [sub_eq_iff_eq_add] at hθ
  simpa only [add_comm] using hθ

/-- The tail decomposition can retain the full uniform prime-power factor
introduced by dilation. -/
theorem exists_vinogradovPolynomialDilation_eq_lowDegreePart_add_scaledTail
    (p a r : ℕ) (H : Polynomial ℤ) (hzero : H.coeff 0 = 0) :
    ∃ θ : Polynomial ℤ,
      vinogradovPolynomialDilation ((p : ℤ) ^ a) H =
        vinogradovLowDegreePart r
            (vinogradovPolynomialDilation ((p : ℤ) ^ a) H) +
          Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
            Polynomial.X ^ (r + 1) * θ := by
  let P := vinogradovPolynomialDilation ((p : ℤ) ^ a) H
  have hPzero : P.coeff 0 = 0 := by
    simp only [P, vinogradovPolynomialDilation,
      Polynomial.comp_C_mul_X_coeff, hzero, pow_zero, mul_one]
  obtain ⟨τ, hτ⟩ :=
    exists_eq_vinogradovLowDegreePart_add_tail r P hPzero
  have htail :
      P - vinogradovLowDegreePart r P = Polynomial.X ^ (r + 1) * τ := by
    calc
      P - vinogradovLowDegreePart r P =
          (vinogradovLowDegreePart r P + Polynomial.X ^ (r + 1) * τ) -
            vinogradovLowDegreePart r P :=
        congrArg (fun Q : Polynomial ℤ ↦
          Q - vinogradovLowDegreePart r P) hτ
      _ = Polynomial.X ^ (r + 1) * τ := by ring
  have hτcoeff : ∀ n : ℕ,
      (p : ℤ) ^ (a * (r + 1)) ∣ τ.coeff n := by
    intro n
    have hdvd := primePower_dvd_coeff_dilation_sub_lowDegreePart
      p a r (n + (r + 1)) H hzero
    change (p : ℤ) ^ (a * (r + 1)) ∣
      (P - vinogradovLowDegreePart r P).coeff (n + (r + 1)) at hdvd
    rw [htail, Polynomial.coeff_X_pow_mul] at hdvd
    exact hdvd
  have hC : Polynomial.C ((p : ℤ) ^ (a * (r + 1))) ∣ τ := by
    rw [Polynomial.C_dvd_iff_dvd_coeff]
    exact hτcoeff
  obtain ⟨θ, hθ⟩ := hC
  refine ⟨θ, ?_⟩
  change P = _
  rw [hτ, hθ]
  ring

/-- Coefficientwise divisibility of the first `r` nonconstant terms produces
an integral low-degree quotient polynomial. -/
theorem exists_vinogradovLowDegreePart_factor
    (r : ℕ) (A : ℤ) (P : Polynomial ℤ)
    (hcoeff : ∀ j : Fin r, A ∣ P.coeff (j.val + 1)) :
    ∃ Ψ : Polynomial ℤ,
      vinogradovLowDegreePart r P = Polynomial.C A * Ψ := by
  choose e he using hcoeff
  let Ψ : Polynomial ℤ :=
    ∑ j : Fin r, Polynomial.C (e j) * Polynomial.X ^ (j.val + 1)
  refine ⟨Ψ, ?_⟩
  unfold vinogradovLowDegreePart Ψ
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [he]
  simp only [map_mul]
  ring

/-- The verified low-degree output of the unit-twisted normalization.
For each transformed row, its first `r` nonconstant dilated coefficients
factor through that row's distinguished prime-power scale.  This theorem
constructs the low-degree `Ψ`; it deliberately makes no claim yet about the
remaining degree-`r+1` tail. -/
theorem exists_vinogradovTranslatedLowDegreePsi
    (p k r a γ M : ℕ)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (hleft : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M])
    (hrowScale : ∀ i : Fin r,
      γ * (k - (i.val + 1)) + a * (i.val + 1) ≤ M) :
    ∃ Ψ : Fin r → Polynomial ℤ,
      ∀ i : Fin r,
        vinogradovLowDegreePart r
            (vinogradovPolynomialDilation ((p : ℤ) ^ a)
              (vinogradovPolynomialMatrixCombination B F i)) =
          Polynomial.C
              ((p : ℤ) ^
                (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
            Ψ i := by
  choose Ψ hΨ using fun i : Fin r ↦
    exists_vinogradovLowDegreePart_factor r
      ((p : ℤ) ^ (γ * (k - (i.val + 1)) + a * (i.val + 1)))
      (vinogradovPolynomialDilation ((p : ℤ) ^ a)
        (vinogradovPolynomialMatrixCombination B F i))
      (fun j ↦
        primePower_dvd_coeff_vinogradovTranslatedMatrixCombination_dilation
          p k r a γ M F Ω B hcoeff hleft hrowScale i j)
  exact ⟨Ψ, hΨ⟩

/-- Paper-facing low-degree normalization for an actual translated spaced
polynomial family.  It constructs an invertible integer row transformation
and the corresponding integral low-degree `Ψ` family.  The assertion stops
at the low-degree projection; absorption of the remaining Taylor tail is the
next analytic-arithmetic obligation. -/
theorem exists_vinogradovTranslatedSpacedLowDegreePsi
    (p c k r a γ M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ)
    (hrowScale : ∀ i : Fin r,
      γ * (k - (i.val + 1)) + a * (i.val + 1) ≤ M) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ Ψ : Fin r → Polynomial ℤ,
        IsUnit
            (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
        ∀ i : Fin r,
          vinogradovLowDegreePart r
              (vinogradovPolynomialDilation ((p : ℤ) ^ a)
                (vinogradovPolynomialMatrixCombination B
                  (fun row ↦
                    Polynomial.C
                        ((ω * (p : ℤ) ^ γ) ^
                          (k - vinogradovBinomialPoint k r row)) *
                      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
                        (vinogradovSpacedPolynomial p c k
                          (vinogradovBinomialPoint k r row) (ψ row))) i)) =
            Polynomial.C
                ((p : ℤ) ^
                  (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
              Ψ i := by
  obtain ⟨Ω, hcoeffRaw, hΩ⟩ :=
    exists_vinogradovTranslatedCoefficientMatrix
      p c k r a γ hrk ω ψ
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  have hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j := by
    intro i j
    simpa only [F, Polynomial.coeff_C_mul] using hcoeffRaw i j
  obtain ⟨B, hleft, hBdet⟩ :=
    exists_vinogradovTranslatedCoefficientMatrix_leftInverse
      p k r c M hrk hkp hc hM ω hω Ω hΩ
  obtain ⟨Ψ, hΨ⟩ :=
    exists_vinogradovTranslatedLowDegreePsi
      p k r a γ M F Ω B hcoeff hleft hrowScale
  refine ⟨B, Ψ, hBdet, ?_⟩
  intro i
  simpa only [F] using hΨ i

/-- The standard far-scale budget bounds every distinguished row scale,
because these scales increase with the low degree when `γ ≤ a`. -/
theorem vinogradovRowScale_le_of_budget
    (k r a γ M : ℕ) (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (i : Fin r) :
    γ * (k - (i.val + 1)) + a * (i.val + 1) ≤ M := by
  have hmr : i.val + 1 ≤ r := Nat.succ_le_iff.mpr i.isLt
  have hsplitk :
      k - (i.val + 1) = (k - r) + (r - (i.val + 1)) := by
    omega
  have hsplitr : r - (i.val + 1) + (i.val + 1) = r := by
    omega
  have hmul :
      γ * (r - (i.val + 1)) ≤ a * (r - (i.val + 1)) :=
    Nat.mul_le_mul_right _ hγa
  rw [hsplitk, Nat.mul_add]
  calc
    γ * (k - r) + γ * (r - (i.val + 1)) + a * (i.val + 1) ≤
        γ * (k - r) + a * (r - (i.val + 1)) + a * (i.val + 1) := by
          omega
    _ = γ * (k - r) + a * r := by
          rw [Nat.add_assoc, ← Nat.mul_add, hsplitr]
    _ ≤ M := hbudget

/-- The degree-dependent aligned scale is maximal in the last low degree
when `γ ≤ a`. -/
theorem vinogradovRowScale_le_last
    (k r a γ : ℕ) (hrk : r ≤ k) (hγa : γ ≤ a)
    (i : Fin r) :
    γ * (k - (i.val + 1)) + a * (i.val + 1) ≤
      γ * (k - r) + a * r := by
  exact vinogradovRowScale_le_of_budget
    k r a γ (γ * (k - r) + a * r) hrk hγa le_rfl i

/-- The quotient polynomial produced from the normalized low-degree row
evaluates like its distinguished monomial modulo the uniform residual
prime-power scale. -/
theorem eval_vinogradovTranslatedLowDegreePsi_modEq_monomial
    (p k r a γ M : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (Ψ : Fin r → Polynomial ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (hleft : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M])
    (hfactor : ∀ i : Fin r,
      vinogradovLowDegreePart r
          (vinogradovPolynomialDilation ((p : ℤ) ^ a)
            (vinogradovPolynomialMatrixCombination B F i)) =
        Polynomial.C
            ((p : ℤ) ^
              (γ * (k - (i.val + 1)) + a * (i.val + 1))) * Ψ i)
    (i : Fin r) (z : ℤ) :
    (Ψ i).eval z ≡ z ^ (i.val + 1)
      [ZMOD (p : ℤ) ^
        (M - (γ * (k - r) + a * r))] := by
  let S : Fin r → ℕ := fun j ↦
    γ * (k - (j.val + 1)) + a * (j.val + 1)
  let R := M - (γ * (k - r) + a * r)
  let P := vinogradovPolynomialDilation ((p : ℤ) ^ a)
    (vinogradovPolynomialMatrixCombination B F i)
  have hSiLast : S i ≤ γ * (k - r) + a * r := by
    exact vinogradovRowScale_le_last k r a γ hrk hγa i
  have hSiR : S i + R ≤ M := by
    dsimp only [R]
    omega
  have hterm : ∀ j : Fin r,
      P.coeff (j.val + 1) * z ^ (j.val + 1) ≡
        (if i = j then (p : ℤ) ^ S i * z ^ (i.val + 1) else 0)
      [ZMOD (p : ℤ) ^ (S i + R)] := by
    intro j
    have hscaled := (hleft i j).mul_left' (c := (p : ℤ) ^ S j)
    have hscaledZ := hscaled.mul_right (z ^ (j.val + 1))
    have hmod :
        (p : ℤ) ^ S j * (B * Ω) i j * z ^ (j.val + 1) ≡
          (p : ℤ) ^ S j * (if i = j then 1 else 0) *
            z ^ (j.val + 1)
        [ZMOD (p : ℤ) ^ (S j + M)] := by
      simpa only [pow_add, mul_assoc] using hscaledZ
    have hexponent : S i + R ≤ S j + M :=
      hSiR.trans (Nat.le_add_left M (S j))
    have hweak := hmod.of_dvd (pow_dvd_pow (p : ℤ) hexponent)
    rw [show P.coeff (j.val + 1) =
        (p : ℤ) ^ S j * (B * Ω) i j by
      exact coeff_vinogradovTranslatedMatrixCombination_dilation
        p k r a γ F Ω B hcoeff i j]
    by_cases hij : i = j
    · subst j
      simpa using hweak
    · simpa only [if_neg hij, mul_zero, zero_mul] using hweak
  have hsum := Int.ModEq.sum
    (s := Finset.univ)
    (f := fun j : Fin r ↦ P.coeff (j.val + 1) * z ^ (j.val + 1))
    (g := fun j : Fin r ↦
      if i = j then (p : ℤ) ^ S i * z ^ (i.val + 1) else 0)
    (fun j _ ↦ hterm j)
  have heval := congrArg (Polynomial.eval z) (hfactor i)
  simp only [eval_vinogradovLowDegreePart, Polynomial.eval_mul,
    Polynomial.eval_C] at heval
  have hscaledEval :
      (p : ℤ) ^ S i * (Ψ i).eval z ≡
        (p : ℤ) ^ S i * z ^ (i.val + 1)
      [ZMOD (p : ℤ) ^ (S i + R)] := by
    rw [← heval]
    simpa only [P, Finset.sum_ite_eq, Finset.mem_univ, if_true] using hsum
  have hcancel :
      (p : ℤ) ^ S i * (Ψ i).eval z ≡
        (p : ℤ) ^ S i * z ^ (i.val + 1)
      [ZMOD (p : ℤ) ^ S i * (p : ℤ) ^ R] := by
    simpa only [pow_add] using hscaledEval
  exact Int.ModEq.mul_left_cancel'
    (pow_ne_zero _ (Int.ofNat_ne_zero.mpr hp)) hcancel

/-- Balanced sums of the quotient family are therefore congruent to the
corresponding pure power sums at the uniform residual scale. -/
theorem vinogradovTranslatedLowDegreePsi_sumDifference_modEq_powerSum
    {s : ℕ} (p k r a γ M : ℕ) (hp : p ≠ 0)
    (hrk : r ≤ k) (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (F : Fin r → Polynomial ℤ)
    (Ω B : Matrix (Fin r) (Fin r) ℤ)
    (Ψ : Fin r → Polynomial ℤ)
    (hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j)
    (hleft : ∀ i j,
      (B * Ω) i j ≡ (if i = j then 1 else 0)
        [ZMOD (p : ℤ) ^ M])
    (hfactor : ∀ i : Fin r,
      vinogradovLowDegreePart r
          (vinogradovPolynomialDilation ((p : ℤ) ^ a)
            (vinogradovPolynomialMatrixCombination B F i)) =
        Polynomial.C
            ((p : ℤ) ^
              (γ * (k - (i.val + 1)) + a * (i.val + 1))) * Ψ i)
    (i : Fin r) (x y : Fin s → ℤ) :
    vinogradovPolynomialSumDifference (Ψ i) x y ≡
      vinogradovPowerSumDifferenceInt x y (i.val + 1)
      [ZMOD (p : ℤ) ^
        (M - (γ * (k - r) + a * r))] := by
  apply Int.ModEq.sub
  · exact Int.ModEq.sum (s := Finset.univ)
      (fun j _ ↦ eval_vinogradovTranslatedLowDegreePsi_modEq_monomial
        p k r a γ M hp hrk hγa hbudget F Ω B Ψ hcoeff hleft hfactor i (x j))
  · exact Int.ModEq.sum (s := Finset.univ)
      (fun j _ ↦ eval_vinogradovTranslatedLowDegreePsi_modEq_monomial
        p k r a γ M hp hrk hγa hbudget F Ω B Ψ hcoeff hleft hfactor i (y j))

/-- Budget-form wrapper for the paper-facing low-degree `Ψ` construction. -/
theorem exists_vinogradovTranslatedSpacedLowDegreePsi_of_budget
    (p c k r a γ M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ Ψ : Fin r → Polynomial ℤ,
        IsUnit
            (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
        ∀ i : Fin r,
          vinogradovLowDegreePart r
              (vinogradovPolynomialDilation ((p : ℤ) ^ a)
                (vinogradovPolynomialMatrixCombination B
                  (fun row ↦
                    Polynomial.C
                        ((ω * (p : ℤ) ^ γ) ^
                          (k - vinogradovBinomialPoint k r row)) *
                      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
                        (vinogradovSpacedPolynomial p c k
                          (vinogradovBinomialPoint k r row) (ψ row))) i)) =
            Polynomial.C
                ((p : ℤ) ^
                  (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
              Ψ i := by
  apply exists_vinogradovTranslatedSpacedLowDegreePsi
    p c k r a γ M hc hrk hkp hM ω hω ψ
  exact vinogradovRowScale_le_of_budget k r a γ M hrk hγa hbudget

/-- Full polynomial shape after the verified low-degree normalization.  The
main term has the expected row-dependent prime-power factor and the residual
tail begins exactly at degree `r+1`.  A separate valuation theorem is still
needed before the tail can be discarded at the ambient modulus. -/
theorem exists_vinogradovTranslatedSpacedDilationNormalForm_of_budget
    (p c k r a γ M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ Ψ θ : Fin r → Polynomial ℤ,
        IsUnit
            (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
        ∀ i : Fin r,
          vinogradovPolynomialDilation ((p : ℤ) ^ a)
                (vinogradovPolynomialMatrixCombination B
                  (fun row ↦
                    Polynomial.C
                        ((ω * (p : ℤ) ^ γ) ^
                          (k - vinogradovBinomialPoint k r row)) *
                      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
                        (vinogradovSpacedPolynomial p c k
                          (vinogradovBinomialPoint k r row) (ψ row))) i) =
            Polynomial.C
                ((p : ℤ) ^
                  (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
              Ψ i + Polynomial.X ^ (r + 1) * θ i := by
  obtain ⟨B, Ψ, hBdet, hlow⟩ :=
    exists_vinogradovTranslatedSpacedLowDegreePsi_of_budget
      p c k r a γ M hc hrk hkp hM hγa hbudget ω hω ψ
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  let P : Fin r → Polynomial ℤ := fun i ↦
    vinogradovPolynomialDilation ((p : ℤ) ^ a)
      (vinogradovPolynomialMatrixCombination B F i)
  have hzero : ∀ i : Fin r, (P i).coeff 0 = 0 := by
    intro i
    rw [show P i = vinogradovPolynomialDilation ((p : ℤ) ^ a)
        (vinogradovPolynomialMatrixCombination B F i) by rfl,
      coeff_vinogradovPolynomialDilation_matrixCombination]
    simp [F, coeff_zero_vinogradovCenteredTaylor]
  choose θ hθ using fun i : Fin r ↦
    exists_eq_vinogradovLowDegreePart_add_tail r (P i) (hzero i)
  refine ⟨B, Ψ, θ, hBdet, ?_⟩
  intro i
  have hlowi :
      vinogradovLowDegreePart r (P i) =
        Polynomial.C
            ((p : ℤ) ^
              (γ * (k - (i.val + 1)) + a * (i.val + 1))) * Ψ i := by
    simpa only [P, F] using hlow i
  rw [show vinogradovPolynomialDilation ((p : ℤ) ^ a)
        (vinogradovPolynomialMatrixCombination B
          (fun row ↦
            Polynomial.C
                ((ω * (p : ℤ) ^ γ) ^
                  (k - vinogradovBinomialPoint k r row)) *
              vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
                (vinogradovSpacedPolynomial p c k
                  (vinogradovBinomialPoint k r row) (ψ row))) i) = P i by rfl,
    hθ i, hlowi]

/-- Strengthening of the dilation normal form which exposes the exact
uniform `p^(a(r+1))` carried by the high-degree tail. -/
theorem exists_vinogradovTranslatedSpacedDilationNormalForm_with_tailScale
    (p c k r a γ M : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p) (hM : 0 < M)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ M)
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) :
    ∃ B : Matrix (Fin r) (Fin r) ℤ,
      ∃ Ψ θ : Fin r → Polynomial ℤ,
        IsUnit
            (Matrix.of (fun i j ↦ (B i j : ZMod (p ^ M)))).det ∧
        ∀ i : Fin r,
          vinogradovPolynomialDilation ((p : ℤ) ^ a)
                (vinogradovPolynomialMatrixCombination B
                  (fun row ↦
                    Polynomial.C
                        ((ω * (p : ℤ) ^ γ) ^
                          (k - vinogradovBinomialPoint k r row)) *
                      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
                        (vinogradovSpacedPolynomial p c k
                          (vinogradovBinomialPoint k r row) (ψ row))) i) =
            Polynomial.C
                ((p : ℤ) ^
                  (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
              Ψ i +
            Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
              Polynomial.X ^ (r + 1) * θ i := by
  obtain ⟨B, Ψ, hBdet, hlow⟩ :=
    exists_vinogradovTranslatedSpacedLowDegreePsi_of_budget
      p c k r a γ M hc hrk hkp hM hγa hbudget ω hω ψ
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  have hFzero : ∀ i : Fin r,
      (vinogradovPolynomialMatrixCombination B F i).coeff 0 = 0 := by
    intro i
    unfold vinogradovPolynomialMatrixCombination
    rw [Polynomial.finset_sum_coeff]
    simp [F, coeff_zero_vinogradovCenteredTaylor]
  choose θ hθ using fun i : Fin r ↦
    exists_vinogradovPolynomialDilation_eq_lowDegreePart_add_scaledTail
      p a r (vinogradovPolynomialMatrixCombination B F i) (hFzero i)
  refine ⟨B, Ψ, θ, hBdet, ?_⟩
  intro i
  have hlowi :
      vinogradovLowDegreePart r
          (vinogradovPolynomialDilation ((p : ℤ) ^ a)
            (vinogradovPolynomialMatrixCombination B F i)) =
        Polynomial.C
            ((p : ℤ) ^
              (γ * (k - (i.val + 1)) + a * (i.val + 1))) * Ψ i := by
    simpa only [F] using hlow i
  simpa only [F, hlowi] using hθ i

/-- The actual translated-spaced algebraic transition.  The unit-twisted
matrix normalization constructs an integral low-degree family `Ψ`; the
dilated high-degree tail vanishes at the ambient modulus; and aligned
prime-power cancellation leaves the `Ψ` system at `vinogradovFarScale`.

This closes the polynomial-congruence part of the far-scale transition.  It
does not yet identify `Ψ` with pure monomials or prove the subsequent
mean-value inequality. -/
theorem exists_vinogradovTranslatedSpacedLowerSystem_to_farScale
    {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∃ Ψ : Fin r → Polynomial ℤ,
      IsVinogradovPolynomialCongruenceSystem p
        (vinogradovFarScale k r a b γ) Ψ x y := by
  let M := (k - r + 1) * b
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  obtain ⟨B, Ψ, θ, _hBdet, hnormal⟩ :=
    exists_vinogradovTranslatedSpacedDilationNormalForm_with_tailScale
      p c k r a γ M hc hrk hkp hambient hγa hbudget ω hω ψ
  have hFsystem :
      IsVinogradovPolynomialCongruenceSystem p M F
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) := by
    intro row
    rw [vinogradovPolynomialSumDifference_C_mul]
    simpa only [mul_zero, F, M] using
      (hsystem row).mul_left
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row))
  have hBFsystem := hFsystem.matrixCombination p M B F
    (fun i ↦ (p : ℤ) ^ a * x i)
    (fun i ↦ (p : ℤ) ^ a * y i)
  have hscaled : ∀ i : Fin r,
      (p : ℤ) ^
            (γ * (k - (i.val + 1)) + a * (i.val + 1)) *
          vinogradovPolynomialSumDifference (Ψ i) x y ≡ 0
        [ZMOD (p : ℤ) ^ M] := by
    intro i
    have hPi := hBFsystem i
    rw [vinogradovPolynomialSumDifference_dilation] at hPi
    have hnormalI :
        vinogradovPolynomialDilation ((p : ℤ) ^ a)
            (vinogradovPolynomialMatrixCombination B F i) =
          Polynomial.C
              ((p : ℤ) ^
                (γ * (k - (i.val + 1)) + a * (i.val + 1))) *
            Ψ i +
          Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
            Polynomial.X ^ (r + 1) * θ i := by
      simpa only [F, M] using hnormal i
    rw [hnormalI, vinogradovPolynomialSumDifference_add,
      vinogradovPolynomialSumDifference_C_mul] at hPi
    have htailRewrite :
        vinogradovPolynomialSumDifference
            (Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
              Polynomial.X ^ (r + 1) * θ i) x y =
          (p : ℤ) ^ (a * (r + 1)) *
            vinogradovPolynomialSumDifference
              (Polynomial.X ^ (r + 1) * θ i) x y := by
      rw [mul_assoc, vinogradovPolynomialSumDifference_C_mul]
    rw [htailRewrite] at hPi
    have htailZero :
        (p : ℤ) ^ (a * (r + 1)) *
            vinogradovPolynomialSumDifference
              (Polynomial.X ^ (r + 1) * θ i) x y ≡ 0
          [ZMOD (p : ℤ) ^ M] := by
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_left
        (pow_dvd_pow (p : ℤ) (by simpa only [M] using htail)) _
    have hmain := hPi.sub htailZero
    simpa only [add_sub_cancel_right, sub_zero] using hmain
  refine ⟨Ψ, ?_⟩
  apply vinogradovAlignedCongruences_to_farScale
    p k r a b γ (Fact.out : p.Prime).ne_zero hrk hγa hbudget
      1 isCoprime_one_right
      (fun i ↦ vinogradovPolynomialSumDifference (Ψ i) x y)
  intro i
  simpa only [vinogradovAlignedFarScaleDifference, one_pow, one_mul] using
    hscaled i

/-- Pure-power-sum form of the translated far-scale transition.  Unlike the
earlier strong-error-vanishing route, this theorem preserves the Taylor
correction valuations, normalizes the resulting unit-twisted matrix, and
uses the constructed low-degree quotient system before removing it modulo
the uniform residual scale. -/
theorem vinogradovUnscaledTranslatedSpacedSystem_to_farScale_via_unitTwist
    {s : ℕ} (p c k r a b γ : ℕ) [Fact p.Prime]
    (hc : 0 < c) (hrk : r ≤ k) (hkp : k < p)
    (hambient : 0 < (k - r + 1) * b)
    (hγa : γ ≤ a)
    (hbudget : γ * (k - r) + a * r ≤ (k - r + 1) * b)
    (htail : (k - r + 1) * b ≤ a * (r + 1))
    (ω : ℤ) (hω : IsCoprime (p : ℤ) ω)
    (ψ : Fin r → Polynomial ℤ) (x y : Fin s → ℤ)
    (hsystem :
      IsVinogradovPolynomialCongruenceSystem p ((k - r + 1) * b)
        (fun row ↦
          vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
            (vinogradovSpacedPolynomial p c k
              (vinogradovBinomialPoint k r row) (ψ row)))
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i)) :
    ∀ i : Fin r,
      vinogradovPowerSumDifferenceInt x y (i.val + 1) ≡ 0
        [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
  let M := (k - r + 1) * b
  let F : Fin r → Polynomial ℤ := fun row ↦
    Polynomial.C
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row)) *
      vinogradovCenteredTaylor (ω * (p : ℤ) ^ γ)
        (vinogradovSpacedPolynomial p c k
          (vinogradovBinomialPoint k r row) (ψ row))
  obtain ⟨Ω, hcoeffRaw, hΩ⟩ :=
    exists_vinogradovTranslatedCoefficientMatrix
      p c k r a γ hrk ω ψ
  have hcoeff : ∀ i j,
      (F i).coeff (j.val + 1) * ((p : ℤ) ^ a) ^ (j.val + 1) =
        (p : ℤ) ^
            (γ * (k - (j.val + 1)) + a * (j.val + 1)) * Ω i j := by
    intro i j
    simpa only [F, Polynomial.coeff_C_mul] using hcoeffRaw i j
  obtain ⟨B, hleft, _hBdet⟩ :=
    exists_vinogradovTranslatedCoefficientMatrix_leftInverse
      p k r c M hrk hkp hc hambient ω hω Ω hΩ
  have hrowScale : ∀ i : Fin r,
      γ * (k - (i.val + 1)) + a * (i.val + 1) ≤ M :=
    vinogradovRowScale_le_of_budget k r a γ M hrk hγa hbudget
  obtain ⟨Ψ, hlow⟩ :=
    exists_vinogradovTranslatedLowDegreePsi
      p k r a γ M F Ω B hcoeff hleft hrowScale
  have hFzero : ∀ i : Fin r,
      (vinogradovPolynomialMatrixCombination B F i).coeff 0 = 0 := by
    intro i
    unfold vinogradovPolynomialMatrixCombination
    rw [Polynomial.finset_sum_coeff]
    simp [F, coeff_zero_vinogradovCenteredTaylor]
  choose θ htailForm using fun i : Fin r ↦
    exists_vinogradovPolynomialDilation_eq_lowDegreePart_add_scaledTail
      p a r (vinogradovPolynomialMatrixCombination B F i) (hFzero i)
  have hnormal : ∀ i : Fin r,
      vinogradovPolynomialDilation ((p : ℤ) ^ a)
          (vinogradovPolynomialMatrixCombination B F i) =
        Polynomial.C
            ((p : ℤ) ^
              (γ * (k - (i.val + 1)) + a * (i.val + 1))) * Ψ i +
          Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
            Polynomial.X ^ (r + 1) * θ i := by
    intro i
    rw [htailForm i, hlow i]
  have hFsystem :
      IsVinogradovPolynomialCongruenceSystem p M F
        (fun i ↦ (p : ℤ) ^ a * x i)
        (fun i ↦ (p : ℤ) ^ a * y i) := by
    intro row
    rw [vinogradovPolynomialSumDifference_C_mul]
    simpa only [mul_zero, F, M] using
      (hsystem row).mul_left
        ((ω * (p : ℤ) ^ γ) ^
          (k - vinogradovBinomialPoint k r row))
  have hBFsystem := hFsystem.matrixCombination p M B F
    (fun i ↦ (p : ℤ) ^ a * x i)
    (fun i ↦ (p : ℤ) ^ a * y i)
  have hscaled : ∀ i : Fin r,
      (p : ℤ) ^
            (γ * (k - (i.val + 1)) + a * (i.val + 1)) *
          vinogradovPolynomialSumDifference (Ψ i) x y ≡ 0
        [ZMOD (p : ℤ) ^ M] := by
    intro i
    have hPi := hBFsystem i
    rw [vinogradovPolynomialSumDifference_dilation, hnormal i,
      vinogradovPolynomialSumDifference_add,
      vinogradovPolynomialSumDifference_C_mul] at hPi
    have htailRewrite :
        vinogradovPolynomialSumDifference
            (Polynomial.C ((p : ℤ) ^ (a * (r + 1))) *
              Polynomial.X ^ (r + 1) * θ i) x y =
          (p : ℤ) ^ (a * (r + 1)) *
            vinogradovPolynomialSumDifference
              (Polynomial.X ^ (r + 1) * θ i) x y := by
      rw [mul_assoc, vinogradovPolynomialSumDifference_C_mul]
    rw [htailRewrite] at hPi
    have htailZero :
        (p : ℤ) ^ (a * (r + 1)) *
            vinogradovPolynomialSumDifference
              (Polynomial.X ^ (r + 1) * θ i) x y ≡ 0
          [ZMOD (p : ℤ) ^ M] := by
      rw [Int.modEq_zero_iff_dvd]
      exact dvd_mul_of_dvd_left
        (pow_dvd_pow (p : ℤ) (by simpa only [M] using htail)) _
    have hmain := hPi.sub htailZero
    simpa only [add_sub_cancel_right, sub_zero] using hmain
  have hΨsystem :
      IsVinogradovPolynomialCongruenceSystem p
        (vinogradovFarScale k r a b γ) Ψ x y := by
    apply vinogradovAlignedCongruences_to_farScale
      p k r a b γ (Fact.out : p.Prime).ne_zero hrk hγa hbudget
        1 isCoprime_one_right
        (fun i ↦ vinogradovPolynomialSumDifference (Ψ i) x y)
    intro i
    simpa only [vinogradovAlignedFarScaleDifference, one_pow, one_mul] using
      hscaled i
  intro i
  have hcompare :=
    vinogradovTranslatedLowDegreePsi_sumDifference_modEq_powerSum
      p k r a γ M (Fact.out : p.Prime).ne_zero hrk hγa hbudget
        F Ω B Ψ hcoeff hleft hlow i x y
  have hcompareFar :
      vinogradovPolynomialSumDifference (Ψ i) x y ≡
        vinogradovPowerSumDifferenceInt x y (i.val + 1)
      [ZMOD (p : ℤ) ^ vinogradovFarScale k r a b γ] := by
    simpa only [M, vinogradovFarScale, Nat.sub_sub, Nat.mul_comm,
      Nat.add_comm] using hcompare
  exact hcompareFar.symm.trans (hΨsystem i)

end

end ZeroFreeRegion.VinogradovKorobov
