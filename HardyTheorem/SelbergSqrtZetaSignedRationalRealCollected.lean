import HardyTheorem.SelbergSqrtZetaSignedCollectedEnergy
import HardyTheorem.SelbergSqrtZetaSignedRationalCollected

/-!
# Compatibility of rational and real-frequency collection

The signed Selberg phase can be collected either by its real logarithmic
frequency or by the positive rational key `l / (m*d)`.  Equal logarithmic
frequencies are exactly equal rational keys on the finite support.  This file
identifies the two collected coefficient systems term by term and transfers
their exact square energy without a cardinality loss.
-/

open Complex
open scoped BigOperators

namespace HardyTheorem

/-- Rational frequency is injective on the actual finite rational support. -/
theorem selbergSqrtZetaSignedRationalFrequency_injOn
    (N X : ℕ) :
    Set.InjOn selbergSqrtZetaSignedRationalFrequency
      (selbergSqrtZetaSignedRationalSupport N X : Set ℚ) := by
  classical
  intro q hq r hr hfrequency
  rcases Finset.mem_image.mp hq with ⟨p, hp, rfl⟩
  rcases Finset.mem_image.mp hr with ⟨s, hs, rfl⟩
  apply
    (selbergSqrtZetaSignedPhaseFrequency_eq_iff_rationalKey_eq
      hp hs).mp
  rw [selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hp,
    selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hs]
  exact hfrequency

/-- Collecting at the real logarithmic frequency of a supported rational key
gives exactly the coefficient collected in that rational fiber. -/
theorem selbergSqrtZetaSignedCollectedCoeff_rationalFrequency
    {N X : ℕ} {q : ℚ}
    (hq : q ∈ selbergSqrtZetaSignedRationalSupport N X) :
    selbergSqrtZetaSignedCollectedCoeff N X
        (selbergSqrtZetaSignedRationalFrequency q) =
      selbergSqrtZetaSignedRationalCoeff N X q := by
  classical
  rcases Finset.mem_image.mp hq with ⟨r, hr, rfl⟩
  unfold selbergSqrtZetaSignedCollectedCoeff
    selbergSqrtZetaSignedRationalCoeff
    selbergSqrtZetaSignedRationalFiber
    MathlibAux.collectedCoefficient
  congr 1
  ext p
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hfrequency⟩
    refine ⟨hp, (selbergSqrtZetaSignedPhaseFrequency_eq_iff_rationalKey_eq
      hp hr).mp ?_⟩
    calc
      selbergSqrtZetaSignedPhaseFrequency p =
          selbergSqrtZetaSignedRationalFrequency
            (selbergSqrtZetaSignedRationalKey r) := hfrequency
      _ = selbergSqrtZetaSignedPhaseFrequency r :=
        (selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hr).symm
  · rintro ⟨hp, hkey⟩
    have hphase :
        selbergSqrtZetaSignedPhaseFrequency p =
          selbergSqrtZetaSignedPhaseFrequency r :=
      (selbergSqrtZetaSignedPhaseFrequency_eq_iff_rationalKey_eq
        hp hr).mpr hkey
    refine ⟨hp, ?_⟩
    calc
      selbergSqrtZetaSignedPhaseFrequency p =
          selbergSqrtZetaSignedPhaseFrequency r := hphase
      _ = selbergSqrtZetaSignedRationalFrequency
          (selbergSqrtZetaSignedRationalKey r) :=
        selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hr

/-- The image of rational frequency support is exactly the support obtained
by collecting the same phase polynomial directly over real frequencies. -/
theorem image_rationalFrequency_rationalSupport
    (N X : ℕ) :
    (selbergSqrtZetaSignedRationalSupport N X).image
        selbergSqrtZetaSignedRationalFrequency =
      selbergSqrtZetaSignedCollectedFrequencySupport N X := by
  classical
  ext omega
  constructor
  · intro homega
    rcases Finset.mem_image.mp homega with ⟨q, hq, hqomega⟩
    rcases Finset.mem_image.mp hq with ⟨p, hp, hpq⟩
    subst q
    unfold selbergSqrtZetaSignedCollectedFrequencySupport
      MathlibAux.collectedFrequencySupport
    apply Finset.mem_image.mpr
    refine ⟨p, hp, ?_⟩
    rw [selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hp]
    exact hqomega
  · intro homega
    unfold selbergSqrtZetaSignedCollectedFrequencySupport
      MathlibAux.collectedFrequencySupport at homega
    rcases Finset.mem_image.mp homega with ⟨p, hp, hpomega⟩
    apply Finset.mem_image.mpr
    refine ⟨selbergSqrtZetaSignedRationalKey p, ?_, ?_⟩
    · exact Finset.mem_image.mpr ⟨p, hp, rfl⟩
    · rw [← hpomega]
      exact
        (selbergSqrtZetaSignedPhaseFrequency_eq_rationalFrequency_key hp).symm

/-- The exact collected square energy is unchanged when the signed Selberg
phase is indexed by rational keys instead of real logarithmic frequencies. -/
theorem sum_normSq_collectedCoeff_eq_rationalCoeff
    (N X : ℕ) :
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff N X omega)) =
      ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by
  classical
  let Q : Finset ℚ := selbergSqrtZetaSignedRationalSupport N X
  let frequency : ℚ → ℝ := selbergSqrtZetaSignedRationalFrequency
  let energy : ℝ → ℝ := fun omega =>
    Complex.normSq (selbergSqrtZetaSignedCollectedCoeff N X omega)
  have hinj : Set.InjOn frequency (Q : Set ℚ) := by
    simpa only [Q, frequency] using
      selbergSqrtZetaSignedRationalFrequency_injOn N X
  calc
    (∑ omega ∈ selbergSqrtZetaSignedCollectedFrequencySupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedCollectedCoeff N X omega)) =
        ∑ omega ∈ Q.image frequency, energy omega := by
      rw [image_rationalFrequency_rationalSupport N X]
    _ = ∑ q ∈ Q, energy (frequency q) :=
      Finset.sum_image hinj
    _ = ∑ q ∈ selbergSqrtZetaSignedRationalSupport N X,
        Complex.normSq
          (selbergSqrtZetaSignedRationalCoeff N X q) := by
      apply Finset.sum_congr rfl
      intro q hq
      dsimp only [energy, frequency]
      rw [selbergSqrtZetaSignedCollectedCoeff_rationalFrequency hq]

end HardyTheorem
