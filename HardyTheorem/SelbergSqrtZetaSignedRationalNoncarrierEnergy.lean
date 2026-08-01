import HardyTheorem.SelbergSqrtZetaSignedRationalCarrierEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalLocalSeparation
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedPairSupport
import HardyTheorem.SelbergSqrtZetaSignedRationalReducedSeparation
import MathlibAux.LocalFrequencySeparationMonotone

/-!
# Local-separation energy after removing the rational carrier

Deleting the ratio-one frequency improves every surviving local separation.
Consequently the noncarrier weighted energy is bounded by the corresponding
terms of the full-support energy, with the carrier term genuinely absent.
-/

open scoped BigOperators

namespace HardyTheorem

/-- The rationally collected polynomial with the distinguished ratio-one
frequency deleted. -/
noncomputable def selbergSqrtZetaSignedRationalNoncarrierPolynomial
    (N X : ℕ) (t : ℝ) : ℂ :=
  MathlibAux.exponentialPolynomial
    (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
    (selbergSqrtZetaSignedRationalCoeff N X)
    selbergSqrtZetaSignedRationalFrequency t

private theorem selbergSqrtZetaSignedRational_pos_of_support_noncarrier
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    0 < q := by
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  exact selbergSqrtZetaSignedRationalKey_pos_of_mem hp

/-- Mapping every positive coprime pair except `(1,1)` back to its rational
key gives exactly the signed rational support with the carrier `q = 1`
deleted. -/
theorem image_selbergSqrtZetaSignedReducedPairKey_reducedPairSupport_erase_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    ((selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1)).image
        selbergSqrtZetaSignedReducedPairKey =
      selbergSqrtZetaSignedRationalNoncarrierSupport N X := by
  classical
  have honeQ : (1 : ℚ) ∈ selbergSqrtZetaSignedRationalSupport N X :=
    one_mem_selbergSqrtZetaSignedRationalSupport hN hX
  have honeP :
      (1, 1) ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X := by
    rw [selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff]
    refine ⟨by norm_num, by norm_num, by norm_num, ?_⟩
    simpa [selbergSqrtZetaSignedReducedPairKey] using honeQ
  ext q
  constructor
  · intro hq
    rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
    have hpP := Finset.mem_of_mem_erase hp
    have hpNe : p ≠ (1, 1) := (Finset.mem_erase.mp hp).1
    have hpKeyFull :
        selbergSqrtZetaSignedReducedPairKey p ∈
          selbergSqrtZetaSignedRationalSupport N X :=
      (selbergSqrtZetaSignedRationalReducedPairSupport_mem_iff.mp hpP).2.2.2
    apply Finset.mem_erase.mpr
    refine ⟨?_, hpKeyFull⟩
    intro hpKeyOne
    apply hpNe
    apply selbergSqrtZetaSignedReducedPairKey_injOn N X hpP honeP
    simpa [selbergSqrtZetaSignedReducedPairKey] using hpKeyOne
  · intro hq
    have hqErase := Finset.mem_erase.mp hq
    have hqPos :=
      selbergSqrtZetaSignedRational_pos_of_support_noncarrier hqErase.2
    let p := selbergSqrtZetaSignedCanonicalReducedPair q
    have hpP : p ∈ selbergSqrtZetaSignedRationalReducedPairSupport N X :=
      Finset.mem_image.mpr ⟨q, hqErase.2, rfl⟩
    have hpKey : selbergSqrtZetaSignedReducedPairKey p = q :=
      selbergSqrtZetaSignedCanonicalReducedPair_key_eq hqPos
    apply Finset.mem_image.mpr
    refine ⟨p, Finset.mem_erase.mpr ⟨?_, hpP⟩, hpKey⟩
    intro hpOne
    apply hqErase.1
    rw [← hpKey, hpOne]
    simp [selbergSqrtZetaSignedReducedPairKey]

/-- Exact reindexing of every finite noncarrier sum by positive coprime
numerator-denominator pairs, with the carrier pair `(1,1)` absent on the
right-hand side. -/
theorem
    sum_selbergSqrtZetaSignedRationalNoncarrierSupport_eq_reducedPairSupport_erase_one
    {M : Type*} [AddCommMonoid M] {N X : ℕ}
    (hN : 1 ≤ N) (hX : 1 ≤ X) (f : ℚ → M) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X, f q) =
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        f (selbergSqrtZetaSignedReducedPairKey p) := by
  rw [←
    image_selbergSqrtZetaSignedReducedPairKey_reducedPairSupport_erase_one hN hX]
  exact Finset.sum_image
    ((selbergSqrtZetaSignedReducedPairKey_injOn N X).mono
      (by
        intro p hp
        exact Finset.mem_of_mem_erase hp))

/-- The unweighted squared-coefficient energy of the genuine noncarrier is
exactly the corresponding positive-coprime-pair sum with `(1,1)` removed. -/
theorem sum_normSq_noncarrier_eq_reducedPairSupport_erase_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q)) =
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X
            (selbergSqrtZetaSignedReducedPairKey p)) := by
  exact
    sum_selbergSqrtZetaSignedRationalNoncarrierSupport_eq_reducedPairSupport_erase_one
      hN hX (fun q =>
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q))

/-- The noncarrier part of the full-support local-separation energy has an
exact arithmetic reindexing over reduced pairs other than `(1,1)`. -/
theorem
    sum_normSq_div_fullLocalSeparation_noncarrier_eq_reducedPairSupport_erase_one
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) =
      ∑ p ∈ (selbergSqrtZetaSignedRationalReducedPairSupport N X).erase (1, 1),
        Complex.normSq
            (selbergSqrtZetaSignedRationalCoeff N X
              (selbergSqrtZetaSignedReducedPairKey p)) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedReducedPairKey p) := by
  exact
    sum_selbergSqrtZetaSignedRationalNoncarrierSupport_eq_reducedPairSupport_erase_one
      hN hX (fun q =>
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q)

/-- Recomputing nearest-neighbour separations after deleting the carrier can
only decrease the local-separation weighted energy of the surviving terms. -/
theorem sum_normSq_div_localFrequencySeparation_noncarrier_le_erase_full
    {N X : ℕ}
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) ≤
      ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q := by
  classical
  have hSubset :
      selbergSqrtZetaSignedRationalNoncarrierSupport N X ⊆
        selbergSqrtZetaSignedRationalSupport N X := by
    intro q hq
    exact Finset.mem_of_mem_erase hq
  have hFull :
      (selbergSqrtZetaSignedRationalSupport N X).Nontrivial :=
    hNoncarrier.mono hSubset
  apply Finset.sum_le_sum
  intro q hq
  have hqFull : q ∈ selbergSqrtZetaSignedRationalSupport N X := hSubset hq
  have hsepFull :
      0 < PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
        (selbergSqrtZetaSignedRationalSupport N X)
        selbergSqrtZetaSignedRationalFrequency q :=
    PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation_pos
      hFull hqFull (selbergSqrtZetaSignedRationalFrequency_injOn N X)
  have hsepMono :=
    PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation_mono_of_subset
      (omega := selbergSqrtZetaSignedRationalFrequency) (n := q)
      hSubset hNoncarrier
  exact div_le_div_of_nonneg_left
    (Complex.normSq_nonneg _) hsepFull hsepMono

/-- The recomputed noncarrier weighted energy plus the original carrier term
is bounded by the full-support weighted energy.  Thus deleting the carrier
genuinely removes its local-separation cost. -/
theorem noncarrierEnergy_add_carrierEnergy_le_fullEnergy
    {N X : ℕ} (hN : 1 ≤ N) (hX : 1 ≤ X)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X).Nontrivial) :
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) +
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency 1 ≤
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q := by
  classical
  let f : ℚ → ℝ := fun q =>
    Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
      PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
        (selbergSqrtZetaSignedRationalSupport N X)
        selbergSqrtZetaSignedRationalFrequency q
  have hone : (1 : ℚ) ∈ selbergSqrtZetaSignedRationalSupport N X :=
    one_mem_selbergSqrtZetaSignedRationalSupport hN hX
  have hsum :
      (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X, f q) +
          f 1 =
        ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X, f q := by
    unfold selbergSqrtZetaSignedRationalNoncarrierSupport
    exact Finset.sum_erase_add _ _ hone
  calc
    (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
            selbergSqrtZetaSignedRationalFrequency q) +
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X 1) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency 1 ≤
      (∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X, f q) +
        f 1 := by
      simpa only [f] using add_le_add_left
        (sum_normSq_div_localFrequencySeparation_noncarrier_le_erase_full
          hNoncarrier) _
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X, f q := hsum
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq (selbergSqrtZetaSignedRationalCoeff N X q) /
          PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
            (selbergSqrtZetaSignedRationalSupport N X)
            selbergSqrtZetaSignedRationalFrequency q := by rfl

/-- Montgomery--Vaughan mean square applied directly after deleting the
carrier frequency.  Both coefficient sums and local separations are computed
on the genuine noncarrier support. -/
theorem
    integral_normSq_selbergSqrtZetaSignedRationalNoncarrierPolynomial_le_localSeparation
    (N X : ℕ) {a b : ℝ} (hab : a ≤ b)
    (hNoncarrier :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X).Nontrivial) :
    (∫ t in a..b,
        Complex.normSq
          (selbergSqrtZetaSignedRationalNoncarrierPolynomial N X t)) ≤
      (b - a) *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq
              (selbergSqrtZetaSignedRationalCoeff N X q) +
        4 * Real.pi *
          ∑ q ∈ selbergSqrtZetaSignedRationalNoncarrierSupport N X,
            Complex.normSq
                (selbergSqrtZetaSignedRationalCoeff N X q) /
              PrimeNumberTheorem.DirichletPolynomial.localFrequencySeparation
                (selbergSqrtZetaSignedRationalNoncarrierSupport N X)
                selbergSqrtZetaSignedRationalFrequency q := by
  have hSubset :
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X : Set ℚ) ⊆
        selbergSqrtZetaSignedRationalSupport N X := by
    intro q hq
    exact Finset.mem_of_mem_erase hq
  have hinj : Set.InjOn selbergSqrtZetaSignedRationalFrequency
      (selbergSqrtZetaSignedRationalNoncarrierSupport N X : Set ℚ) :=
    (selbergSqrtZetaSignedRationalFrequency_injOn N X).mono hSubset
  have hmean :=
    PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum_meanSquare_le_localSeparation
      (S := selbergSqrtZetaSignedRationalNoncarrierSupport N X)
      (c := selbergSqrtZetaSignedRationalCoeff N X)
      (omega := selbergSqrtZetaSignedRationalFrequency)
      hab hNoncarrier hinj
  simpa only [selbergSqrtZetaSignedRationalNoncarrierPolynomial,
    MathlibAux.exponentialPolynomial,
    PrimeNumberTheorem.DirichletPolynomial.finiteExponentialSum,
    Complex.normSq_eq_norm_sq] using hmean

end HardyTheorem
