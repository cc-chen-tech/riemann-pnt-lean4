import HardyTheorem.SelbergSqrtZetaSignedRationalReducedRatio

/-!
# Finite coprime-ray reindexing of the signed Selberg coefficient energy

The exact rational coefficient energy contains pairs `(k,l)` and `(k',l')`
with `l*k' = l'*k`.  The reduced-ratio theorem identifies these as two
positive scalar multiples of one coprime ray `(a,b)`.  This file performs the
finite reindexing needed by the next arithmetic estimate: every off-diagonal
term is represented once by `(a,b,d,e)`, with `d ≠ e`.
-/

open scoped BigOperators

namespace HardyTheorem

/-- One coprime numerator-denominator ray together with two scale variables. -/
structure SelbergSqrtZetaSignedCoprimeRayScales where
  numerator : ℕ
  denominator : ℕ
  leftScale : ℕ
  rightScale : ℕ
deriving DecidableEq

/-- The denominator-numerator pair represented by the left scale. -/
def selbergSqrtZetaSignedCoprimeRayScales_leftPair
    (x : SelbergSqrtZetaSignedCoprimeRayScales) : ℕ × ℕ :=
  (x.denominator * x.leftScale, x.numerator * x.leftScale)

/-- The denominator-numerator pair represented by the right scale. -/
def selbergSqrtZetaSignedCoprimeRayScales_rightPair
    (x : SelbergSqrtZetaSignedCoprimeRayScales) : ℕ × ℕ :=
  (x.denominator * x.rightScale, x.numerator * x.rightScale)

private def selbergSqrtZetaSignedCoprimeRayScalesOfPairs
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    SelbergSqrtZetaSignedCoprimeRayScales where
  numerator := pr.1.2 / Nat.gcd pr.1.2 pr.1.1
  denominator := pr.1.1 / Nat.gcd pr.1.2 pr.1.1
  leftScale := Nat.gcd pr.1.2 pr.1.1
  rightScale := Nat.gcd pr.2.2 pr.2.1

/-- The finite support of distinct supported pairs satisfying the
cross-product equation. -/
private noncomputable def
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport
    (N X : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let S := selbergSqrtZetaSignedDenominatorNumeratorSupport N X
  (S.product S).filter fun pr =>
    pr.1 ≠ pr.2 ∧ pr.1.2 * pr.2.1 = pr.2.2 * pr.1.1

/-- The actual finite support of coprime rays and unequal scale pairs appearing
in the signed rational coefficient off-diagonal correlation. -/
noncomputable def
    selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport
    (N X : ℕ) : Finset SelbergSqrtZetaSignedCoprimeRayScales :=
  (selbergSqrtZetaSignedRationalOffDiagonalPairSupport N X).image
    selbergSqrtZetaSignedCoprimeRayScalesOfPairs

private theorem
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts
    {N X : ℕ} {pr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr :
      pr ∈ selbergSqrtZetaSignedRationalOffDiagonalPairSupport N X) :
    pr.1 ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X ∧
      pr.2 ∈ selbergSqrtZetaSignedDenominatorNumeratorSupport N X ∧
      pr.1 ≠ pr.2 ∧
      pr.1.2 * pr.2.1 = pr.2.2 * pr.1.1 := by
  rcases Finset.mem_filter.mp hpr with ⟨hprod, hdistinct, hcross⟩
  exact ⟨(Finset.mem_product.mp hprod).1,
    (Finset.mem_product.mp hprod).2, hdistinct, hcross⟩

private theorem selbergSqrtZetaSignedCoprimeRayScalesOfPairs_leftPair
    (pr : (ℕ × ℕ) × (ℕ × ℕ)) :
    selbergSqrtZetaSignedCoprimeRayScales_leftPair
        (selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr) =
      pr.1 := by
  apply Prod.ext
  · exact Nat.div_mul_cancel (Nat.gcd_dvd_right pr.1.2 pr.1.1)
  · exact Nat.div_mul_cancel (Nat.gcd_dvd_left pr.1.2 pr.1.1)

private theorem selbergSqrtZetaSignedCoprimeRayScalesOfPairs_rightPair
    {k l k' l' : ℕ} (hk : 0 < k) (hk' : 0 < k')
    (hcross : l * k' = l' * k) :
    selbergSqrtZetaSignedCoprimeRayScales_rightPair
        (selbergSqrtZetaSignedCoprimeRayScalesOfPairs
          ((k, l), (k', l'))) =
      (k', l') := by
  rcases
      (crossProduct_eq_iff_exists_coprime_scales hk hk').mp hcross with
    ⟨a, b, d, e, hab, hb, hl, hkFactor, hl', hk'Factor⟩
  have hd : 0 < d := by
    have hdNe : d ≠ 0 := by
      intro hd
      rw [hd, mul_zero] at hkFactor
      omega
    exact Nat.pos_of_ne_zero hdNe
  have he : 0 < e := by
    have heNe : e ≠ 0 := by
      intro he
      rw [he, mul_zero] at hk'Factor
      omega
    exact Nat.pos_of_ne_zero heNe
  have hgcdLeft : Nat.gcd l k = d := by
    calc
      Nat.gcd l k = Nat.gcd (a * d) (b * d) := by rw [hl, hkFactor]
      _ = Nat.gcd a b * d := Nat.gcd_mul_right a d b
      _ = d := by rw [hab.gcd_eq_one, one_mul]
  have hgcdRight : Nat.gcd l' k' = e := by
    calc
      Nat.gcd l' k' = Nat.gcd (a * e) (b * e) := by rw [hl', hk'Factor]
      _ = Nat.gcd a b * e := Nat.gcd_mul_right a e b
      _ = e := by rw [hab.gcd_eq_one, one_mul]
  change
    (k / Nat.gcd l k * Nat.gcd l' k',
      l / Nat.gcd l k * Nat.gcd l' k') = (k', l')
  rw [hgcdLeft, hgcdRight, hkFactor, hl,
    Nat.mul_div_left b hd, Nat.mul_div_left a hd, hk'Factor, hl']

private theorem
    selbergSqrtZetaSignedCoprimeRayScalesOfPairs_injOn
    {N X : ℕ} {pr qr : (ℕ × ℕ) × (ℕ × ℕ)}
    (hpr :
      pr ∈ selbergSqrtZetaSignedRationalOffDiagonalPairSupport N X)
    (hqr :
      qr ∈ selbergSqrtZetaSignedRationalOffDiagonalPairSupport N X)
    (heq :
      selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr =
        selbergSqrtZetaSignedCoprimeRayScalesOfPairs qr) :
    pr = qr := by
  have hprFacts :=
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hpr
  have hqrFacts :=
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hqr
  have hprLeftPos : 0 < pr.1.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.1).1
  have hprRightPos : 0 < pr.2.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.2.1).1
  have hqrLeftPos : 0 < qr.1.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hqrFacts.1).1
  have hqrRightPos : 0 < qr.2.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hqrFacts.2.1).1
  have hleft : pr.1 = qr.1 := by
    calc
      pr.1 =
          selbergSqrtZetaSignedCoprimeRayScales_leftPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr) :=
        (selbergSqrtZetaSignedCoprimeRayScalesOfPairs_leftPair pr).symm
      _ =
          selbergSqrtZetaSignedCoprimeRayScales_leftPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs qr) := by rw [heq]
      _ = qr.1 :=
        selbergSqrtZetaSignedCoprimeRayScalesOfPairs_leftPair qr
  have hright : pr.2 = qr.2 := by
    calc
      pr.2 =
          selbergSqrtZetaSignedCoprimeRayScales_rightPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr) :=
        (selbergSqrtZetaSignedCoprimeRayScalesOfPairs_rightPair
          hprLeftPos hprRightPos hprFacts.2.2.2).symm
      _ =
          selbergSqrtZetaSignedCoprimeRayScales_rightPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs qr) := by rw [heq]
      _ = qr.2 :=
        selbergSqrtZetaSignedCoprimeRayScalesOfPairs_rightPair
          hqrLeftPos hqrRightPos hqrFacts.2.2.2
  exact Prod.ext hleft hright

/-- Every ray in the reindexed support has coprime numerator and denominator. -/
theorem selbergSqrtZetaSignedCoprimeRayScales_coprime
    {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    Nat.Coprime x.numerator x.denominator := by
  rcases Finset.mem_image.mp hx with ⟨pr, hpr, rfl⟩
  have hprFacts :=
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hpr
  have hk : 0 < pr.1.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.1).1
  have hgcd : 0 < Nat.gcd pr.1.2 pr.1.1 :=
    Nat.gcd_pos_of_pos_right pr.1.2 hk
  exact Nat.coprime_div_gcd_div_gcd hgcd

/-- Every ray in the reindexed support has positive denominator. -/
theorem selbergSqrtZetaSignedCoprimeRayScales_denominator_pos
    {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    0 < x.denominator := by
  rcases Finset.mem_image.mp hx with ⟨pr, hpr, rfl⟩
  have hprFacts :=
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hpr
  have hk : 0 < pr.1.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.1).1
  have hkFactor :
      pr.1.1 =
        pr.1.1 / Nat.gcd pr.1.2 pr.1.1 *
          Nat.gcd pr.1.2 pr.1.1 :=
    (Nat.div_mul_cancel (Nat.gcd_dvd_right pr.1.2 pr.1.1)).symm
  have hne :
      pr.1.1 / Nat.gcd pr.1.2 pr.1.1 ≠ 0 := by
    intro hzero
    rw [hzero, zero_mul] at hkFactor
    omega
  exact Nat.pos_of_ne_zero hne

/-- The scale data carried by the finite support are positive and distinct,
and both reconstructed pairs belong to the actual coefficient support. -/
theorem selbergSqrtZetaSignedCoprimeRayScales_scale_facts
    {N X : ℕ} {x : SelbergSqrtZetaSignedCoprimeRayScales}
    (hx :
      x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X) :
    0 < x.leftScale ∧ 0 < x.rightScale ∧
      x.leftScale ≠ x.rightScale ∧
      selbergSqrtZetaSignedCoprimeRayScales_leftPair x ∈
        selbergSqrtZetaSignedDenominatorNumeratorSupport N X ∧
      selbergSqrtZetaSignedCoprimeRayScales_rightPair x ∈
        selbergSqrtZetaSignedDenominatorNumeratorSupport N X := by
  rcases Finset.mem_image.mp hx with ⟨pr, hpr, rfl⟩
  have hprFacts :=
    selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hpr
  have hleftPos : 0 < pr.1.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.1).1
  have hrightPos : 0 < pr.2.1 :=
    selbergSqrtZetaSignedDenominator_pos_of_mem
      (Finset.mem_product.mp hprFacts.2.1).1
  have hleftScale : 0 < Nat.gcd pr.1.2 pr.1.1 :=
    Nat.gcd_pos_of_pos_right pr.1.2 hleftPos
  have hrightScale : 0 < Nat.gcd pr.2.2 pr.2.1 :=
    Nat.gcd_pos_of_pos_right pr.2.2 hrightPos
  have hleft :=
    selbergSqrtZetaSignedCoprimeRayScalesOfPairs_leftPair pr
  have hright :=
    selbergSqrtZetaSignedCoprimeRayScalesOfPairs_rightPair
      hleftPos hrightPos hprFacts.2.2.2
  refine ⟨hleftScale, hrightScale, ?_, ?_, ?_⟩
  · intro hscale
    apply hprFacts.2.2.1
    calc
      pr.1 =
          selbergSqrtZetaSignedCoprimeRayScales_leftPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr) := hleft.symm
      _ =
          selbergSqrtZetaSignedCoprimeRayScales_rightPair
            (selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr) := by
        simp only [selbergSqrtZetaSignedCoprimeRayScales_leftPair,
          selbergSqrtZetaSignedCoprimeRayScales_rightPair,
          selbergSqrtZetaSignedCoprimeRayScalesOfPairs]
        have hscale' :
            Nat.gcd pr.1.2 pr.1.1 = Nat.gcd pr.2.2 pr.2.1 := by
          simpa only [selbergSqrtZetaSignedCoprimeRayScalesOfPairs] using
            hscale
        rw [hscale']
      _ = pr.2 := hright
  · rw [hleft]
    exact hprFacts.1
  · rw [hright]
    exact hprFacts.2.1

private theorem
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_pairSupportSum
    (N X : ℕ) :
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X =
      ∑ pr ∈ selbergSqrtZetaSignedRationalOffDiagonalPairSupport N X,
        selbergSqrtZetaSignedRationalPairCoeff N X pr.1 *
          selbergSqrtZetaSignedRationalPairCoeff N X pr.2 := by
  classical
  let S := selbergSqrtZetaSignedDenominatorNumeratorSupport N X
  let coeff := selbergSqrtZetaSignedRationalPairCoeff N X
  unfold selbergSqrtZetaSignedRationalCoefficientOffDiagonal
  change
    (∑ p ∈ S, ∑ r ∈ S.erase p,
      if p.2 * r.1 = r.2 * p.1 then coeff p * coeff r else 0) =
      ∑ pr ∈ (S.product S).filter (fun pr =>
          pr.1 ≠ pr.2 ∧ pr.1.2 * pr.2.1 = pr.2.2 * pr.1.1),
        coeff pr.1 * coeff pr.2
  rw [Finset.sum_filter]
  calc
    (∑ p ∈ S, ∑ r ∈ S.erase p,
        if p.2 * r.1 = r.2 * p.1 then coeff p * coeff r else 0) =
        ∑ p ∈ S, ∑ r ∈ S,
          if p ≠ r ∧ p.2 * r.1 = r.2 * p.1
          then coeff p * coeff r
          else 0 := by
      apply Finset.sum_congr rfl
      intro p hp
      rw [← Finset.filter_ne' S p, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r hr
      by_cases hpr : p = r
      · subst r
        simp
      · simp [hpr, Ne.symm hpr]
    _ = ∑ pr ∈ S.product S,
        if pr.1 ≠ pr.2 ∧ pr.1.2 * pr.2.1 = pr.2.2 * pr.1.1
        then coeff pr.1 * coeff pr.2
        else 0 :=
      (Finset.sum_product S S (fun pr : (ℕ × ℕ) × (ℕ × ℕ) =>
        if pr.1 ≠ pr.2 ∧ pr.1.2 * pr.2.1 = pr.2.2 * pr.1.1
        then coeff pr.1 * coeff pr.2
        else 0)).symm

/-- Exact finite coprime-ray reindexing of the actual off-diagonal coefficient
correlation.  Each term is indexed once by a coprime ray `(a,b)` and two
distinct positive scales; no absolute value or fiber-cardinality loss is
introduced. -/
theorem
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_coprimeRayScaleSum
    (N X : ℕ) :
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal N X =
      ∑ x ∈ selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X,
        selbergSqrtZetaSignedRationalPairCoeff N X
            (selbergSqrtZetaSignedCoprimeRayScales_leftPair x) *
          selbergSqrtZetaSignedRationalPairCoeff N X
            (selbergSqrtZetaSignedCoprimeRayScales_rightPair x) := by
  classical
  rw [
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_pairSupportSum]
  refine Finset.sum_bij
    (fun pr _hpr => selbergSqrtZetaSignedCoprimeRayScalesOfPairs pr)
    ?_ ?_ ?_ ?_
  · intro pr hpr
    exact Finset.mem_image.mpr ⟨pr, hpr, rfl⟩
  · intro pr hpr qr hqr heq
    exact selbergSqrtZetaSignedCoprimeRayScalesOfPairs_injOn hpr hqr heq
  · intro x hx
    rcases Finset.mem_image.mp hx with ⟨pr, hpr, rfl⟩
    exact ⟨pr, hpr, rfl⟩
  · intro pr hpr
    have hprFacts :=
      selbergSqrtZetaSignedRationalOffDiagonalPairSupport_facts hpr
    have hleftPos : 0 < pr.1.1 :=
      selbergSqrtZetaSignedDenominator_pos_of_mem
        (Finset.mem_product.mp hprFacts.1).1
    have hrightPos : 0 < pr.2.1 :=
      selbergSqrtZetaSignedDenominator_pos_of_mem
        (Finset.mem_product.mp hprFacts.2.1).1
    rw [selbergSqrtZetaSignedCoprimeRayScalesOfPairs_leftPair,
      selbergSqrtZetaSignedCoprimeRayScalesOfPairs_rightPair
        hleftPos hrightPos hprFacts.2.2.2]

/-- Direct coefficient-energy form of the finite coprime-ray reindexing.  The
only term left for the arithmetic estimate is the explicit ray-scale sum. -/
theorem
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_coprimeRayScaleSum
    (N X : ℕ) :
    (∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      (∑ k ∈ selbergSqrtZetaSignedDenominatorSupport N X,
          Complex.normSq
            (selbergSqrtZetaSignedDenominatorCollectedCoeff N X k)) *
        (∑ l ∈ selbergSqrtZetaSignedNumeratorSupport X,
          Complex.normSq (selbergSqrtZetaSignedNumeratorCoeff X l)) +
        ∑ x ∈
            selbergSqrtZetaSignedRationalOffDiagonalCoprimeRayScaleSupport N X,
          selbergSqrtZetaSignedRationalPairCoeff N X
              (selbergSqrtZetaSignedCoprimeRayScales_leftPair x) *
            selbergSqrtZetaSignedRationalPairCoeff N X
              (selbergSqrtZetaSignedCoprimeRayScales_rightPair x) := by
  rw [
    sum_normSq_selbergSqrtZetaSignedRationalCoeff_eq_product_add_offDiagonal,
    selbergSqrtZetaSignedRationalCoefficientOffDiagonal_eq_coprimeRayScaleSum]

end HardyTheorem
