import HardyTheorem.SelbergSqrtZetaSignedRationalCoeffCoprimeRayReindex

/-!
# Canonical reduced-pair support for the signed Selberg rational model

Every rational key in the signed support is positive.  This file replaces
that finite rational support by the unique positive coprime numerator and
denominator pair of each key, and proves an exact finite-sum reindexing.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The canonical positive reduced numerator-denominator pair of a rational
key.  Positivity is supplied by membership in the signed rational support. -/
def selbergSqrtZetaSignedCanonicalReducedPair (q : ℚ) : ℕ × ℕ :=
  (q.num.natAbs, q.den)

/-- The rational key represented by a natural numerator-denominator pair. -/
noncomputable def selbergSqrtZetaSignedReducedPairKey
    (p : ℕ × ℕ) : ℚ :=
  (p.1 : ℚ) / (p.2 : ℚ)

/-- The canonical finite support of positive coprime pairs representing the
actual signed Selberg rational support. -/
noncomputable def selbergSqrtZetaSignedRationalReducedPairSupport
    (N X : ℕ) : Finset (ℕ × ℕ) :=
  (selbergSqrtZetaSignedRationalSupport N X).image
    selbergSqrtZetaSignedCanonicalReducedPair

private theorem selbergSqrtZetaSignedRational_pos_of_support
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    0 < q := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact selbergSqrtZetaSignedRationalKey_pos_of_mem hp

/-- Taking the key of the canonical reduced pair recovers a positive
rational exactly. -/
theorem selbergSqrtZetaSignedCanonicalReducedPair_key_eq
    {q : ℚ} (hq : 0 < q) :
    selbergSqrtZetaSignedReducedPairKey
        (selbergSqrtZetaSignedCanonicalReducedPair q) =
      q := by
  have hnum : 0 < q.num := Rat.num_pos.mpr hq
  unfold selbergSqrtZetaSignedReducedPairKey
    selbergSqrtZetaSignedCanonicalReducedPair
  calc
    (q.num.natAbs : ℚ) / (q.den : ℚ) =
        (q.num : ℚ) / (q.den : ℚ) := by
      congr 1
      rw [← Int.cast_natCast]
      exact congrArg (fun z : ℤ => (z : ℚ))
        (Int.natAbs_of_nonneg hnum.le)
    _ = q := q.num_div_den

/-- A positive coprime natural pair is recovered exactly after passing to its
rational key and taking the canonical reduced pair. -/
theorem selbergSqrtZetaSignedCanonicalReducedPair_key_of_pos_coprime
    {p : ℕ × ℕ} (_ha : 0 < p.1) (hb : 0 < p.2)
    (hab : Nat.Coprime p.1 p.2) :
    selbergSqrtZetaSignedCanonicalReducedPair
        (selbergSqrtZetaSignedReducedPairKey p) =
      p := by
  have hnum :
      (((p.1 : ℚ) / (p.2 : ℚ)).num : ℤ) = (p.1 : ℤ) := by
    simpa using
      (Rat.num_div_eq_of_coprime
        (a := (p.1 : ℤ)) (b := (p.2 : ℤ))
        (by exact_mod_cast hb) (by simpa using hab))
  have hden :
      ((((p.1 : ℚ) / (p.2 : ℚ)).den : ℕ) : ℤ) = (p.2 : ℤ) := by
    simpa using
      (Rat.den_div_eq_of_coprime
        (a := (p.1 : ℤ)) (b := (p.2 : ℤ))
        (by exact_mod_cast hb) (by simpa using hab))
  apply Prod.ext
  · unfold selbergSqrtZetaSignedCanonicalReducedPair
      selbergSqrtZetaSignedReducedPairKey
    simp only [hnum, Int.natAbs_natCast]
  · unfold selbergSqrtZetaSignedCanonicalReducedPair
      selbergSqrtZetaSignedReducedPairKey
    exact_mod_cast hden

/-- Membership in the canonical pair support is exactly positivity,
coprimality, and membership of the represented rational key in the original
support. -/
theorem selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff
    {N X : ℕ} {p : ℕ × ℕ} :
    p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X ↔
      0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
        selbergSqrtZetaSignedReducedPairKey p ∈
          selbergSqrtZetaSignedRationalSupport N X := by
  constructor
  · intro hp
    rcases Finset.mem_image.mp hp with ⟨q, hq, rfl⟩
    have hqPos := selbergSqrtZetaSignedRational_pos_of_support hq
    have hnum : 0 < q.num := Rat.num_pos.mpr hqPos
    refine ⟨Int.natAbs_pos.mpr hnum.ne', q.den_pos, q.reduced, ?_⟩
    rwa [selbergSqrtZetaSignedCanonicalReducedPair_key_eq hqPos]
  · rintro ⟨ha, hb, hab, hpKey⟩
    apply Finset.mem_image.mpr
    refine ⟨selbergSqrtZetaSignedReducedPairKey p, hpKey, ?_⟩
    exact
      selbergSqrtZetaSignedCanonicalReducedPair_key_of_pos_coprime
        ha hb hab

/-- The reduced-pair key is injective on the canonical finite support. -/
theorem selbergSqrtZetaSignedReducedPairKey_injOn
    (N X : ℕ) :
    Set.InjOn selbergSqrtZetaSignedReducedPairKey
      (selbergSqrtZetaSignedRationalReducedPairSupport N X : Set (ℕ × ℕ)) := by
  intro p hp r hr hkey
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp
  have hrFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hr
  calc
    p =
        selbergSqrtZetaSignedCanonicalReducedPair
          (selbergSqrtZetaSignedReducedPairKey p) :=
      (selbergSqrtZetaSignedCanonicalReducedPair_key_of_pos_coprime
        hpFacts.1 hpFacts.2.1 hpFacts.2.2.1).symm
    _ =
        selbergSqrtZetaSignedCanonicalReducedPair
          (selbergSqrtZetaSignedReducedPairKey r) := by rw [hkey]
    _ = r :=
      selbergSqrtZetaSignedCanonicalReducedPair_key_of_pos_coprime
        hrFacts.1 hrFacts.2.1 hrFacts.2.2.1

/-- Every supported rational key has one and only one positive coprime pair
in the canonical pair support. -/
theorem selbergSqrtZetaSignedRationalSupport_unique_reducedPair
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    ∃! p : ℕ × ℕ,
      p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X ∧
        0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 ∧
          selbergSqrtZetaSignedReducedPairKey p = q := by
  let p := selbergSqrtZetaSignedCanonicalReducedPair q
  have hqPos := selbergSqrtZetaSignedRational_pos_of_support hq
  have hpKey :
      selbergSqrtZetaSignedReducedPairKey p = q :=
    selbergSqrtZetaSignedCanonicalReducedPair_key_eq hqPos
  have hpMem :
      p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X :=
    Finset.mem_image.mpr ⟨q, hq, rfl⟩
  have hpFacts :=
    selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpMem
  refine ⟨p, ⟨hpMem, hpFacts.1, hpFacts.2.1, hpFacts.2.2.1, hpKey⟩, ?_⟩
  intro r hr
  apply selbergSqrtZetaSignedReducedPairKey_injOn N X
  · exact hr.1
  · exact hpMem
  · rw [hr.2.2.2.2, hpKey]

/-- Mapping the canonical pair support back to rational keys gives exactly
the original finite rational support. -/
theorem image_selbergSqrtZetaSignedReducedPairKey_reducedPairSupport
    (N X : ℕ) :
    (selbergSqrtZetaSignedRationalReducedPairSupport N X).image
        selbergSqrtZetaSignedReducedPairKey =
      selbergSqrtZetaSignedRationalSupport N X := by
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    exact
      (selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hp).2.2.2
  · intro hq
    have hqPos := selbergSqrtZetaSignedRational_pos_of_support hq
    apply Finset.mem_image.mpr
    refine ⟨selbergSqrtZetaSignedCanonicalReducedPair q, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨q, hq, rfl⟩
    · exact selbergSqrtZetaSignedCanonicalReducedPair_key_eq hqPos

/-- Exact finite-sum reindexing from rational keys to their unique positive
coprime numerator-denominator pairs. -/
theorem sum_selbergSqrtZetaSignedRationalSupport_eq_reducedPairSupport
    {M : Type*} [AddCommMonoid M] (N X : ℕ) (f : ℚ → M) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X, f q) =
      ∑ p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X,
        f (selbergSqrtZetaSignedReducedPairKey p) := by
  rw [← image_selbergSqrtZetaSignedReducedPairKey_reducedPairSupport]
  exact Finset.sum_image (selbergSqrtZetaSignedReducedPairKey_injOn N X)

end HardyTheorem
