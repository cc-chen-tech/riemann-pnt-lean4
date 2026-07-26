import ZeroFreeRegion.VinogradovKorobov.VinogradovLifting

open scoped BigOperators

namespace ZeroFreeRegion.VinogradovKorobov

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

/-- Every tuple is paired with itself as an integer Vinogradov solution. -/
theorem isVinogradovSolutionNat_refl (k s X : ℕ)
    (x : Fin s → Fin X) :
    IsVinogradovSolutionNat k s X x x := by
  intro j
  rfl

/-- The integer Vinogradov solution count is bounded by the number of all
ordered pairs of `s`-tuples. -/
theorem vinogradovSolutionCountNat_le_total (k s X : ℕ) :
    vinogradovSolutionCountNat k s X ≤ X ^ (2 * s) := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    ∑ x : Fin s → Fin X,
        ((Finset.univ.filter fun y : Fin s → Fin X ↦
          IsVinogradovSolutionNat k s X x y).card) ≤
        ∑ _x : Fin s → Fin X,
          Fintype.card (Fin s → Fin X) := by
      apply Finset.sum_le_sum
      intro x hx
      exact Finset.card_le_card (Finset.filter_subset _ _)
    _ = X ^ (2 * s) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin]
      change X ^ s * X ^ s = X ^ (2 * s)
      rw [← pow_add]
      congr 2
      omega

/-- Diagonal tuple pairs give at least `X^s` Vinogradov solutions. -/
theorem pow_le_vinogradovSolutionCountNat (k s X : ℕ) :
    X ^ s ≤ vinogradovSolutionCountNat k s X := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    X ^ s = ∑ _x : Fin s → Fin X, 1 := by simp
    _ ≤ ∑ x : Fin s → Fin X,
        ((Finset.univ.filter fun y : Fin s → Fin X ↦
          IsVinogradovSolutionNat k s X x y).card) := by
      apply Finset.sum_le_sum
      intro x hx
      apply Finset.one_le_card.mpr
      exact ⟨x, by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact isVinogradovSolutionNat_refl k s X x⟩

/-- With one variable on each side and at least the first-power equation,
the Vinogradov system says exactly that the two entries are equal. -/
theorem isVinogradovSolutionNat_one_iff {k X : ℕ} (hk : 0 < k)
    (x y : Fin 1 → Fin X) :
    IsVinogradovSolutionNat k 1 X x y ↔ x = y := by
  constructor
  · intro h
    funext i
    have hi : i = 0 := Subsingleton.elim i 0
    subst i
    have hsum := h (⟨0, hk⟩ : Fin k)
    have hval : (x 0).val + 1 = (y 0).val + 1 := by
      simpa [vinogradovPowerSumNat] using hsum
    apply Fin.ext
    omega
  · rintro rfl
    exact isVinogradovSolutionNat_refl k 1 X x

/-- The first nonempty mean value is exact: with one variable on each side,
there are precisely `X` solutions. -/
theorem vinogradovSolutionCountNat_one (k X : ℕ) (hk : 0 < k) :
    vinogradovSolutionCountNat k 1 X = X := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    ∑ x : Fin 1 → Fin X,
        ((Finset.univ.filter fun y : Fin 1 → Fin X ↦
          IsVinogradovSolutionNat k 1 X x y).card) =
        ∑ _x : Fin 1 → Fin X, 1 := by
      apply Finset.sum_congr rfl
      intro x hx
      have hfilter :
          Finset.univ.filter (fun y : Fin 1 → Fin X ↦
            IsVinogradovSolutionNat k 1 X x y) = {x} := by
        ext y
        simp only [Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_singleton]
        simpa [eq_comm] using isVinogradovSolutionNat_one_iff hk x y
      rw [hfilter]
      simp
    _ = X := by simp

/-- Consequently, the normalized finite Fourier second moment is exactly `X`
once the modulus is larger than the degree-`k` power range. -/
theorem normalizedVinogradovMomentMod_one (Q k X : ℕ) [NeZero Q]
    (hk : 0 < k) (hX : 1 ≤ X) (hQ : X ^ k < Q) :
    normalizedVinogradovMomentMod Q k 1 X = (X : ℂ) := by
  rw [normalizedVinogradovMomentMod_eq_natCount_of_topScale Q k 1 X hX]
  · simp [vinogradovSolutionCountNat_one k X hk]
  · simpa using hQ

/-- For a fixed left tuple, solutions of any positive-degree Vinogradov system
are determined by the first `n` entries of a right tuple of length `n + 1`.
The first-power equation determines the final entry. -/
theorem fixed_left_solution_count_le (k n X : ℕ) (hk : 0 < k)
    (x : Fin (n + 1) → Fin X) :
    (Finset.univ.filter fun y : Fin (n + 1) → Fin X ↦
      IsVinogradovSolutionNat k (n + 1) X x y).card ≤ X ^ n := by
  classical
  let init : (Fin (n + 1) → Fin X) → (Fin n → Fin X) :=
    fun y i ↦ y i.castSucc
  have hinj : Set.InjOn init
      (Finset.univ.filter fun y : Fin (n + 1) → Fin X ↦
        IsVinogradovSolutionNat k (n + 1) X x y) := by
    intro y hy z hz hinit
    have hySol : IsVinogradovSolutionNat k (n + 1) X x y := by
      change y ∈ Finset.univ.filter (fun y : Fin (n + 1) → Fin X ↦
        IsVinogradovSolutionNat k (n + 1) X x y) at hy
      exact (Finset.mem_filter.mp hy).2
    have hzSol : IsVinogradovSolutionNat k (n + 1) X x z := by
      change z ∈ Finset.univ.filter (fun y : Fin (n + 1) → Fin X ↦
        IsVinogradovSolutionNat k (n + 1) X x y) at hz
      exact (Finset.mem_filter.mp hz).2
    have hpow : vinogradovPowerSumNat y (⟨0, hk⟩ : Fin k) =
        vinogradovPowerSumNat z (⟨0, hk⟩ : Fin k) :=
      (hySol ⟨0, hk⟩).symm.trans (hzSol ⟨0, hk⟩)
    have hsumOne : (∑ i : Fin (n + 1), ((y i).val + 1)) =
        ∑ i : Fin (n + 1), ((z i).val + 1) := by
      simpa [vinogradovPowerSumNat] using hpow
    have hsum : (∑ i : Fin (n + 1), (y i).val) =
        ∑ i : Fin (n + 1), (z i).val := by
      simp only [Finset.sum_add_distrib, Finset.sum_const,
        Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] at hsumOne
      omega
    rw [Fin.sum_univ_castSucc, Fin.sum_univ_castSucc] at hsum
    have hpref : (∑ i : Fin n, (y i.castSucc).val) =
        ∑ i : Fin n, (z i.castSucc).val := by
      apply Fintype.sum_congr
      intro i
      exact congrArg Fin.val (congrFun hinit i)
    have hlast : y (Fin.last n) = z (Fin.last n) := by
      apply Fin.ext
      omega
    funext i
    exact Fin.lastCases hlast (fun j ↦ congrFun hinit j) i
  have hcard := Finset.card_le_card_of_injOn init
    (s := Finset.univ.filter fun y : Fin (n + 1) → Fin X ↦
      IsVinogradovSolutionNat k (n + 1) X x y)
    (t := Finset.univ) (by intro y hy; simp) hinj
  simpa using hcard

/-- Degree one already saves one full power of `X` over the trivial count:
for `s = n + 1`, there are at most `X^(2n+1)` solutions. Higher-degree
systems satisfy the same bound because they include the first-power equation. -/
theorem vinogradovSolutionCountNat_le_firstPower
    (k n X : ℕ) (hk : 0 < k) :
    vinogradovSolutionCountNat k (n + 1) X ≤ X ^ (2 * n + 1) := by
  classical
  unfold vinogradovSolutionCountNat
  calc
    ∑ x : Fin (n + 1) → Fin X,
        ((Finset.univ.filter fun y : Fin (n + 1) → Fin X ↦
          IsVinogradovSolutionNat k (n + 1) X x y).card) ≤
        ∑ _x : Fin (n + 1) → Fin X, X ^ n := by
      apply Finset.sum_le_sum
      intro x hx
      exact fixed_left_solution_count_le k n X hk x
    _ = X ^ (2 * n + 1) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        Fintype.card_fun, Fintype.card_fin]
      change X ^ (n + 1) * X ^ n = X ^ (2 * n + 1)
      rw [← pow_add]
      apply congrArg
      omega

/-- The first-power counting saving transfers directly to the complete finite
Weyl moment whenever the modulus is large enough to avoid wraparound. -/
theorem norm_normalizedVinogradovMomentMod_le_firstPower
    (Q k n X : ℕ) [NeZero Q] (hk : 0 < k) (hX : 1 ≤ X)
    (hQ : (n + 1) * X ^ k < Q) :
    ‖normalizedVinogradovMomentMod Q k (n + 1) X‖ ≤
      (X : ℝ) ^ (2 * n + 1) := by
  rw [normalizedVinogradovMomentMod_eq_natCount_of_topScale
    Q k (n + 1) X hX hQ]
  exact_mod_cast vinogradovSolutionCountNat_le_firstPower k n X hk

end

end ZeroFreeRegion.VinogradovKorobov
