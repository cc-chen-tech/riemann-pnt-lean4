import MathlibAux.GaussianBucketSchur
import PrimeNumberTheorem.VKEdgeHighZeroBucketEnergy

open Complex Filter
open scoped BigOperators

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# Gaussian energy of the high zeta-zero buckets

This module combines the collision-safe bucket square energy with the
Gaussian Schur estimate.  It controls all cross interactions between high
zero ordinates without assuming that distinct zeros have a minimum spacing.
-/

/-- Absolute coefficient of one multiplicity-weighted explicit-formula zero
term. -/
noncomputable def zeroReciprocalMultiplicityCoefficient (rho : ℂ) : ℝ :=
  (analyticOrderNatAt riemannZeta rho : ℝ) / ‖rho‖

/-- Gaussian quadratic energy of all zeta zeros in the unit ordinate buckets
from `H` through `N`. -/
noncomputable def zeroOrdinateBucketGaussianEnergy
    (H N : ℕ) (m : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc H N,
    ∑ k ∈ Finset.Icc H N,
      ∑ rho ∈ zeroOrdinateUnitBucket n,
        ∑ tau ∈ zeroOrdinateUnitBucket k,
          zeroReciprocalMultiplicityCoefficient rho *
            zeroReciprocalMultiplicityCoefficient tau *
              Real.exp (-m * (rho.im - tau.im) ^ 2)

private theorem zeroReciprocalMultiplicityCoefficient_nonneg (rho : ℂ) :
    0 ≤ zeroReciprocalMultiplicityCoefficient rho := by
  unfold zeroReciprocalMultiplicityCoefficient
  exact div_nonneg (Nat.cast_nonneg _) (norm_nonneg _)

private theorem bucket_frequency_gap
    {n k : ℕ} {rho tau : ℂ}
    (hrho : rho ∈ zeroOrdinateUnitBucket n)
    (htau : tau ∈ zeroOrdinateUnitBucket k) :
    (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |rho.im - tau.im|) := by
  have hrhoBounds := (Finset.mem_filter.mp hrho).2
  have htauBounds := (Finset.mem_filter.mp htau).2
  calc
    (((Nat.dist n k - 1 : ℕ) : ℝ) ≤
        |(|rho.im| - |tau.im|)|) :=
      MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
        hrhoBounds.1 hrhoBounds.2 htauBounds.1 htauBounds.2
    _ ≤ |rho.im - tau.im| := abs_abs_sub_abs_le_abs_sub _ _

private theorem bucket_pair_gaussian_sum_le
    (n k : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    (∑ rho ∈ zeroOrdinateUnitBucket n,
        ∑ tau ∈ zeroOrdinateUnitBucket k,
          zeroReciprocalMultiplicityCoefficient rho *
            zeroReciprocalMultiplicityCoefficient tau *
              Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
      zeroOrdinateUnitBucketCoefficientMass n *
        zeroOrdinateUnitBucketCoefficientMass k *
          MathlibAux.gaussianBucketKernel n k := by
  calc
    (∑ rho ∈ zeroOrdinateUnitBucket n,
        ∑ tau ∈ zeroOrdinateUnitBucket k,
          zeroReciprocalMultiplicityCoefficient rho *
            zeroReciprocalMultiplicityCoefficient tau *
              Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
        ∑ rho ∈ zeroOrdinateUnitBucket n,
          ∑ tau ∈ zeroOrdinateUnitBucket k,
            zeroReciprocalMultiplicityCoefficient rho *
              zeroReciprocalMultiplicityCoefficient tau *
                MathlibAux.gaussianBucketKernel n k := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply Finset.sum_le_sum
      intro tau htau
      apply mul_le_mul_of_nonneg_left
      · exact MathlibAux.exp_neg_mul_sq_le_gaussianBucketKernel hm
          (bucket_frequency_gap hrho htau)
      · exact mul_nonneg
          (zeroReciprocalMultiplicityCoefficient_nonneg rho)
          (zeroReciprocalMultiplicityCoefficient_nonneg tau)
    _ = zeroOrdinateUnitBucketCoefficientMass n *
        zeroOrdinateUnitBucketCoefficientMass k *
          MathlibAux.gaussianBucketKernel n k := by
      let c : ℂ → ℝ := fun z =>
        (analyticOrderNatAt riemannZeta z : ℝ) / ‖z‖
      let G : ℝ := MathlibAux.gaussianBucketKernel n k
      change
        (∑ rho ∈ zeroOrdinateUnitBucket n,
          ∑ tau ∈ zeroOrdinateUnitBucket k,
            c rho * c tau * G) =
          (∑ rho ∈ zeroOrdinateUnitBucket n, c rho) *
            (∑ tau ∈ zeroOrdinateUnitBucket k, c tau) * G
      calc
        (∑ rho ∈ zeroOrdinateUnitBucket n,
            ∑ tau ∈ zeroOrdinateUnitBucket k,
              c rho * c tau * G) =
            ∑ rho ∈ zeroOrdinateUnitBucket n,
              c rho *
                ((∑ tau ∈ zeroOrdinateUnitBucket k, c tau) * G) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          calc
            (∑ tau ∈ zeroOrdinateUnitBucket k,
                c rho * c tau * G) =
                (∑ tau ∈ zeroOrdinateUnitBucket k,
                  c rho * c tau) * G := by
              rw [Finset.sum_mul]
            _ = (c rho *
                  (∑ tau ∈ zeroOrdinateUnitBucket k, c tau)) * G := by
              rw [Finset.mul_sum]
          ring
        _ = (∑ rho ∈ zeroOrdinateUnitBucket n, c rho) *
              ((∑ tau ∈ zeroOrdinateUnitBucket k, c tau) * G) := by
          exact
            (Finset.sum_mul (zeroOrdinateUnitBucket n) c
              ((∑ tau ∈ zeroOrdinateUnitBucket k, c tau) * G)).symm
        _ = (∑ rho ∈ zeroOrdinateUnitBucket n, c rho) *
              (∑ tau ∈ zeroOrdinateUnitBucket k, c tau) * G := by
          ring

/-- The complete finite Gaussian interaction of high zeta zeros is bounded
by the collision-safe square energy of their unit buckets. -/
theorem zeroOrdinateBucketGaussianEnergy_le
    (H N : ℕ) {m : ℝ} (hm : 1 ≤ m) :
    zeroOrdinateBucketGaussianEnergy H N m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ n ∈ Finset.Icc H N,
          zeroOrdinateUnitBucketCoefficientMass n ^ 2 := by
  unfold zeroOrdinateBucketGaussianEnergy
  calc
    (∑ n ∈ Finset.Icc H N,
        ∑ k ∈ Finset.Icc H N,
          ∑ rho ∈ zeroOrdinateUnitBucket n,
            ∑ tau ∈ zeroOrdinateUnitBucket k,
              zeroReciprocalMultiplicityCoefficient rho *
                zeroReciprocalMultiplicityCoefficient tau *
                  Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
        ∑ n ∈ Finset.Icc H N,
          ∑ k ∈ Finset.Icc H N,
            zeroOrdinateUnitBucketCoefficientMass n *
              zeroOrdinateUnitBucketCoefficientMass k *
                MathlibAux.gaussianBucketKernel n k := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      exact bucket_pair_gaussian_sum_le n k hm
    _ ≤ MathlibAux.gaussianBucketSchurConstant *
        ∑ n ∈ Finset.Icc H N,
          zeroOrdinateUnitBucketCoefficientMass n ^ 2 :=
      MathlibAux.sum_mul_gaussianBucketKernel_le
        (Finset.Icc H N) zeroOrdinateUnitBucketCoefficientMass

/-- Uniformly for every Gaussian width `m ≥ 1`, the interaction energy of
all sufficiently high finite zero buckets is arbitrarily small. -/
theorem eventually_zeroOrdinateBucketGaussianEnergy_lt
    {eta : ℝ} (heta : 0 < eta) :
    ∀ᶠ H : ℕ in atTop,
      ∀ N : ℕ, H ≤ N →
        ∀ m : ℝ, 1 ≤ m →
          zeroOrdinateBucketGaussianEnergy H N m < eta := by
  let C : ℝ := MathlibAux.gaussianBucketSchurConstant
  have hC : 0 < C := MathlibAux.gaussianBucketSchurConstant_pos
  have hetaC : 0 < eta / C := div_pos heta hC
  have htail :=
    eventually_sum_Icc_sq_zeroOrdinateUnitBucketCoefficientMass_lt hetaC
  filter_upwards [htail] with H hH
  intro N hHN m hm
  have henergy :=
    zeroOrdinateBucketGaussianEnergy_le H N hm
  have hsmall := hH N hHN
  have hmul :
      C *
          (∑ n ∈ Finset.Icc H N,
            zeroOrdinateUnitBucketCoefficientMass n ^ 2) <
        C * (eta / C) :=
    mul_lt_mul_of_pos_left hsmall hC
  have hcancel : C * (eta / C) = eta := by
    field_simp [hC.ne']
  exact henergy.trans_lt (hmul.trans_eq hcancel)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
