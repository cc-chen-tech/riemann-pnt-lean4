import PrimeNumberTheorem.VKEdgeHighZeroGaussianEnergy
import PrimeNumberTheorem.VKEdgeZeroClusterCoercivity
import PrimeNumberTheorem.PositiveFourierKernel
import PrimeNumberTheorem.VKEdgePiOverTwoGaussianMean
import Mathlib.Probability.Distributions.Gaussian.Real

open Complex
open MeasureTheory ProbabilityTheory
open scoped BigOperators ComplexConjugate

namespace PrimeNumberTheorem
namespace VKEdgePiOverTwo

noncomputable section

/-!
# One-step dynamic zeta-zero packet extraction

The packet below is an actual subset of the height-`T` nontrivial zeta zeros
outside the current dominant set `S`.  Unit ordinate buckets absorb arbitrary
near-collisions internally.  A large Gaussian majorant energy therefore
forces one new, disjoint packet with quantitative frozen coefficient mass.

This is the combinatorial extraction layer.  It does not identify the
majorant with the full moving-window complement `L²` energy; that analytic
bridge must account for real-part drift explicitly.
-/

/-- Fourier transform of the normalized Gaussian, in the convention used by
the finite exponential-sum kernel. -/
theorem fourierKernel_normalizedGaussian
    {m : ℝ} (hm : 0 < m) (xi : ℝ) :
    DirichletPolynomial.fourierKernel (normalizedGaussian m) xi =
      (Real.exp (-m * xi ^ 2) : ℂ) := by
  let v : NNReal := ⟨2 * m, by positivity⟩
  have hv : v ≠ 0 := by
    intro hv0
    have : (v : ℝ) = 0 :=
      congrArg (fun z : NNReal => (z : ℝ)) hv0
    dsimp [v] at this
    linarith
  have hpim : 0 < Real.pi * m := mul_pos Real.pi_pos hm
  have hsqrt :
      Real.sqrt (2 * Real.pi * (v : ℝ)) =
        2 * Real.sqrt (Real.pi * m) := by
    apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
      (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))).mp
    rw [Real.sq_sqrt (by positivity),
      mul_pow, Real.sq_sqrt hpim.le]
    dsimp [v]
    ring
  have hpdf (x : ℝ) :
      gaussianPDFReal 0 v x = normalizedGaussian m x := by
    unfold gaussianPDFReal normalizedGaussian
    rw [hsqrt]
    have hdenom : (2 * (v : ℝ)) = 4 * m := by
      dsimp [v]
      ring
    rw [hdenom]
    simp only [sub_zero]
    rw [inv_mul_eq_div]
  have hchar := charFun_gaussianReal (μ := 0) (v := v) xi
  rw [charFun_apply_real,
    integral_gaussianReal_eq_integral_smul hv] at hchar
  unfold DirichletPolynomial.fourierKernel
  calc
    (∫ t : ℝ,
        (normalizedGaussian m t : ℂ) *
          Complex.exp (Complex.I * (xi * t))) =
        ∫ t : ℝ,
          gaussianPDFReal 0 v t •
            Complex.exp (xi * t * Complex.I) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with t
      rw [hpdf]
      simp only [Complex.real_smul]
      congr 2
      ring
    _ = Complex.exp (xi * 0 * Complex.I -
          (v : ℝ) * xi ^ 2 / 2) := hchar
    _ = (Real.exp (-m * xi ^ 2) : ℂ) := by
      dsimp [v]
      rw [ofReal_exp]
      congr 1
      push_cast
      ring

/-- The actual complementary zeta zeros at height `T` lying in the absolute
ordinate unit bucket `n`. -/
noncomputable def dynamicComplementZeroPacket
    (S : Finset ℂ) (T : ℝ) (n : ℕ) : Finset ℂ :=
  zeroOrdinateUnitBucket n ∩ (nontrivialZerosFinset T \ S)

/-- Frozen multiplicity-weighted coefficient mass of one complementary
packet at logarithmic center `a` and reference exponent `beta`. -/
noncomputable def dynamicComplementPacketCoefficientMass
    (S : Finset ℂ) (T beta a : ℝ) (n : ℕ) : ℝ :=
  ∑ rho ∈ dynamicComplementZeroPacket S T n,
    ‖finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a rho‖

/-- Positive Gaussian majorant for interactions among complementary packets
whose bucket indices lie in `K`. -/
noncomputable def dynamicComplementGaussianMajorantEnergy
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (m : ℝ) : ℝ :=
  ∑ n ∈ K,
    ∑ k ∈ K,
      ∑ rho ∈ dynamicComplementZeroPacket S T n,
        ∑ tau ∈ dynamicComplementZeroPacket S T k,
          ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta a rho‖ *
            ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta a tau‖ *
            Real.exp (-m * (rho.im - tau.im) ^ 2)

/-- Sigma-indexed union of the inspected complementary packets.  The bucket
index remains part of the type, so the later extraction certificate does not
lose packet ownership. -/
noncomputable def dynamicComplementPacketIndexSet
    (S : Finset ℂ) (T : ℝ) (K : Finset ℕ) :
    Finset (Σ _n : ℕ, ℂ) :=
  K.sigma fun n => dynamicComplementZeroPacket S T n

/-- Gaussian-weighted second moment of the frozen complementary
exponential sum over the inspected packet range. -/
noncomputable def dynamicComplementFrozenGaussianSecondMoment
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (m : ℝ) : ℝ :=
  ∫ t : ℝ, normalizedGaussian m t *
    ‖DirichletPolynomial.finiteExponentialSum
      (dynamicComplementPacketIndexSet S T K)
      (fun z => finiteZeroClusterCoefficientAt
        (analyticOrderNatAt riemannZeta) beta a z.2)
      (fun z => z.2.im) t‖ ^ 2

/-- Gaussian second moment of the frozen complementary sum after twisting its
coefficients to the logarithmic window center `a`. -/
noncomputable def dynamicComplementCenteredFrozenGaussianSecondMoment
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ) (m : ℝ) : ℝ :=
  ∫ t : ℝ, normalizedGaussian m t *
    ‖DirichletPolynomial.finiteExponentialSum
      (dynamicComplementPacketIndexSet S T K)
      (DirichletPolynomial.phaseTwist
        (fun z => finiteZeroClusterCoefficientAt
          (analyticOrderNatAt riemannZeta) beta a z.2)
        (fun z => z.2.im) a)
      (fun z => z.2.im) t‖ ^ 2

/-- The frozen Gaussian `L²` energy of the actual finite-height complement is
bounded by the positive packet majorant. -/
theorem dynamicComplementFrozenGaussianSecondMoment_le_majorant
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
    {m : ℝ} (hm : 0 < m) :
    dynamicComplementFrozenGaussianSecondMoment S T beta a K m ≤
      dynamicComplementGaussianMajorantEnergy S T beta a K m := by
  let I : Finset (Σ _n : ℕ, ℂ) :=
    dynamicComplementPacketIndexSet S T K
  let c : (Σ _n : ℕ, ℂ) → ℂ := fun z =>
    finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2
  let omega : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.im
  let E : ℝ :=
    dynamicComplementFrozenGaussianSecondMoment S T beta a K m
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, dynamicComplementFrozenGaussianSecondMoment]
    exact integral_nonneg fun t =>
      mul_nonneg (normalizedGaussian_pos hm t).le (sq_nonneg _)
  have hform :=
    DirichletPolynomial.finiteFourierKernelForm_eq_integral_normSq
      (S := I) (c := c) (omega := omega)
      (g := normalizedGaussian m)
      (integrable_normalizedGaussian hm)
  have hnormForm :
      ‖DirichletPolynomial.finiteFourierKernelForm
          I c omega (normalizedGaussian m)‖ = E := by
    rw [hform, norm_real, Real.norm_eq_abs]
    have hnonneg :
        0 ≤ ∫ t : ℝ, normalizedGaussian m t *
          ‖DirichletPolynomial.finiteExponentialSum I c omega t‖ ^ 2 := by
      simpa [E, I, c, omega,
        dynamicComplementFrozenGaussianSecondMoment] using hE_nonneg
    rw [abs_of_nonneg hnonneg]
    rfl
  calc
    dynamicComplementFrozenGaussianSecondMoment S T beta a K m =
        ‖DirichletPolynomial.finiteFourierKernelForm
          I c omega (normalizedGaussian m)‖ := hnormForm.symm
    _ = ‖∑ z ∈ I, ∑ w ∈ I,
          conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ := by
      unfold DirichletPolynomial.finiteFourierKernelForm
      simp_rw [fourierKernel_normalizedGaussian hm]
    _ ≤ ∑ z ∈ I, ‖∑ w ∈ I,
          conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ I, ∑ w ∈ I,
          ‖conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro z hz
      exact norm_sum_le _ _
    _ = ∑ z ∈ I, ∑ w ∈ I,
          ‖c z‖ * ‖c w‖ *
            Real.exp (-m * (omega z - omega w) ^ 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      rw [norm_mul, norm_mul, norm_conj, norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 2
      ring
    _ = dynamicComplementGaussianMajorantEnergy
          S T beta a K m := by
      dsimp [I, c, omega, dynamicComplementPacketIndexSet]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ rho ∈ dynamicComplementZeroPacket S T n,
            ∑ w ∈ K.sigma fun k =>
              dynamicComplementZeroPacket S T k,
              ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a rho‖ *
                ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a w.2‖ *
                Real.exp (-m * (rho.im - w.2.im) ^ 2)) =
            ∑ rho ∈ dynamicComplementZeroPacket S T n,
              ∑ k ∈ K,
                ∑ tau ∈ dynamicComplementZeroPacket S T k,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ *
                    ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a tau‖ *
                    Real.exp (-m * (rho.im - tau.im) ^ 2) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [Finset.sum_sigma]
        _ = ∑ k ∈ K,
              ∑ rho ∈ dynamicComplementZeroPacket S T n,
                ∑ tau ∈ dynamicComplementZeroPacket S T k,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ *
                    ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a tau‖ *
                    Real.exp (-m * (rho.im - tau.im) ^ 2) := by
          rw [Finset.sum_comm]

/-- Center phase does not change coefficient norms, so the centered frozen
Gaussian second moment obeys the same packet majorant. -/
theorem dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
    {m : ℝ} (hm : 0 < m) :
    dynamicComplementCenteredFrozenGaussianSecondMoment
        S T beta a K m ≤
      dynamicComplementGaussianMajorantEnergy S T beta a K m := by
  let I : Finset (Σ _n : ℕ, ℂ) :=
    dynamicComplementPacketIndexSet S T K
  let base : (Σ _n : ℕ, ℂ) → ℂ := fun z =>
    finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a z.2
  let omega : (Σ _n : ℕ, ℂ) → ℝ := fun z => z.2.im
  let c : (Σ _n : ℕ, ℂ) → ℂ :=
    DirichletPolynomial.phaseTwist base omega a
  let E : ℝ :=
    dynamicComplementCenteredFrozenGaussianSecondMoment
      S T beta a K m
  have hphaseNorm (z : Σ _n : ℕ, ℂ) :
      ‖c z‖ = ‖base z‖ := by
    simp [c, DirichletPolynomial.phaseTwist, Complex.norm_exp]
  have hE_nonneg : 0 ≤ E := by
    dsimp [E, dynamicComplementCenteredFrozenGaussianSecondMoment]
    exact integral_nonneg fun t =>
      mul_nonneg (normalizedGaussian_pos hm t).le (sq_nonneg _)
  have hform :=
    DirichletPolynomial.finiteFourierKernelForm_eq_integral_normSq
      (S := I) (c := c) (omega := omega)
      (g := normalizedGaussian m)
      (integrable_normalizedGaussian hm)
  have hnormForm :
      ‖DirichletPolynomial.finiteFourierKernelForm
          I c omega (normalizedGaussian m)‖ = E := by
    rw [hform, norm_real, Real.norm_eq_abs]
    have hnonneg :
        0 ≤ ∫ t : ℝ, normalizedGaussian m t *
          ‖DirichletPolynomial.finiteExponentialSum I c omega t‖ ^ 2 := by
      simpa [E, I, c, base, omega,
        dynamicComplementCenteredFrozenGaussianSecondMoment] using
          hE_nonneg
    rw [abs_of_nonneg hnonneg]
    rfl
  calc
    dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m =
        ‖DirichletPolynomial.finiteFourierKernelForm
          I c omega (normalizedGaussian m)‖ := hnormForm.symm
    _ = ‖∑ z ∈ I, ∑ w ∈ I,
          conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ := by
      unfold DirichletPolynomial.finiteFourierKernelForm
      simp_rw [fourierKernel_normalizedGaussian hm]
    _ ≤ ∑ z ∈ I, ‖∑ w ∈ I,
          conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ :=
      norm_sum_le _ _
    _ ≤ ∑ z ∈ I, ∑ w ∈ I,
          ‖conj (c z) * c w *
            (Real.exp (-m * (omega w - omega z) ^ 2) : ℂ)‖ := by
      apply Finset.sum_le_sum
      intro z hz
      exact norm_sum_le _ _
    _ = ∑ z ∈ I, ∑ w ∈ I,
          ‖c z‖ * ‖c w‖ *
            Real.exp (-m * (omega z - omega w) ^ 2) := by
      apply Finset.sum_congr rfl
      intro z hz
      apply Finset.sum_congr rfl
      intro w hw
      rw [norm_mul, norm_mul, norm_conj, norm_real,
        Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 2
      ring
    _ = ∑ z ∈ I, ∑ w ∈ I,
          ‖base z‖ * ‖base w‖ *
            Real.exp (-m * (omega z - omega w) ^ 2) := by
      simp_rw [hphaseNorm]
    _ = dynamicComplementGaussianMajorantEnergy
          S T beta a K m := by
      dsimp [I, base, omega, dynamicComplementPacketIndexSet]
      rw [Finset.sum_sigma]
      apply Finset.sum_congr rfl
      intro n hn
      calc
        (∑ rho ∈ dynamicComplementZeroPacket S T n,
            ∑ w ∈ K.sigma fun k =>
              dynamicComplementZeroPacket S T k,
              ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a rho‖ *
                ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a w.2‖ *
                Real.exp (-m * (rho.im - w.2.im) ^ 2)) =
            ∑ rho ∈ dynamicComplementZeroPacket S T n,
              ∑ k ∈ K,
                ∑ tau ∈ dynamicComplementZeroPacket S T k,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ *
                    ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a tau‖ *
                    Real.exp (-m * (rho.im - tau.im) ^ 2) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          rw [Finset.sum_sigma]
        _ = ∑ k ∈ K,
              ∑ rho ∈ dynamicComplementZeroPacket S T n,
                ∑ tau ∈ dynamicComplementZeroPacket S T k,
                  ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a rho‖ *
                    ‖finiteZeroClusterCoefficientAt
                      (analyticOrderNatAt riemannZeta) beta a tau‖ *
                    Real.exp (-m * (rho.im - tau.im) ^ 2) := by
          rw [Finset.sum_comm]

private theorem dynamicComplementZeroPacket_frequency_gap
    {S : Finset ℂ} {T : ℝ} {n k : ℕ} {rho tau : ℂ}
    (hrho : rho ∈ dynamicComplementZeroPacket S T n)
    (htau : tau ∈ dynamicComplementZeroPacket S T k) :
    (((Nat.dist n k - 1 : ℕ) : ℝ) ≤ |rho.im - tau.im|) := by
  have hrhoBucket : rho ∈ zeroOrdinateUnitBucket n :=
    (Finset.mem_inter.mp hrho).1
  have htauBucket : tau ∈ zeroOrdinateUnitBucket k :=
    (Finset.mem_inter.mp htau).1
  have hrhoBounds := (Finset.mem_filter.mp hrhoBucket).2
  have htauBounds := (Finset.mem_filter.mp htauBucket).2
  calc
    (((Nat.dist n k - 1 : ℕ) : ℝ) ≤
        |(|rho.im| - |tau.im|)|) :=
      MathlibAux.natDist_sub_one_le_abs_sub_of_mem_unit
        hrhoBounds.1 hrhoBounds.2 htauBounds.1 htauBounds.2
    _ ≤ |rho.im - tau.im| := abs_abs_sub_abs_le_abs_sub _ _

private theorem dynamicComplementPacket_pair_sum_le
    (S : Finset ℂ) (T beta a : ℝ) (n k : ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    (∑ rho ∈ dynamicComplementZeroPacket S T n,
        ∑ tau ∈ dynamicComplementZeroPacket S T k,
          ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta a rho‖ *
            ‖finiteZeroClusterCoefficientAt
              (analyticOrderNatAt riemannZeta) beta a tau‖ *
            Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
      dynamicComplementPacketCoefficientMass S T beta a n *
        dynamicComplementPacketCoefficientMass S T beta a k *
        MathlibAux.gaussianBucketKernel n k := by
  let c : ℂ → ℝ := fun rho =>
    ‖finiteZeroClusterCoefficientAt
      (analyticOrderNatAt riemannZeta) beta a rho‖
  let G : ℝ := MathlibAux.gaussianBucketKernel n k
  calc
    (∑ rho ∈ dynamicComplementZeroPacket S T n,
        ∑ tau ∈ dynamicComplementZeroPacket S T k,
          c rho * c tau *
            Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
        ∑ rho ∈ dynamicComplementZeroPacket S T n,
          ∑ tau ∈ dynamicComplementZeroPacket S T k,
            c rho * c tau * G := by
      apply Finset.sum_le_sum
      intro rho hrho
      apply Finset.sum_le_sum
      intro tau htau
      apply mul_le_mul_of_nonneg_left
      · exact MathlibAux.exp_neg_mul_sq_le_gaussianBucketKernel hm
          (dynamicComplementZeroPacket_frequency_gap hrho htau)
      · exact mul_nonneg (norm_nonneg _) (norm_nonneg _)
    _ = (∑ rho ∈ dynamicComplementZeroPacket S T n, c rho) *
          (∑ tau ∈ dynamicComplementZeroPacket S T k, c tau) * G := by
      calc
        (∑ rho ∈ dynamicComplementZeroPacket S T n,
            ∑ tau ∈ dynamicComplementZeroPacket S T k,
              c rho * c tau * G) =
            ∑ rho ∈ dynamicComplementZeroPacket S T n,
              c rho *
                ((∑ tau ∈ dynamicComplementZeroPacket S T k, c tau) * G) := by
          apply Finset.sum_congr rfl
          intro rho hrho
          calc
            (∑ tau ∈ dynamicComplementZeroPacket S T k,
                c rho * c tau * G) =
                (∑ tau ∈ dynamicComplementZeroPacket S T k,
                  c rho * c tau) * G := by
              rw [Finset.sum_mul]
            _ = (c rho *
                  (∑ tau ∈ dynamicComplementZeroPacket S T k, c tau)) * G := by
              rw [Finset.mul_sum]
          ring
        _ = (∑ rho ∈ dynamicComplementZeroPacket S T n, c rho) *
              ((∑ tau ∈ dynamicComplementZeroPacket S T k, c tau) * G) := by
          exact
            (Finset.sum_mul (dynamicComplementZeroPacket S T n) c
              ((∑ tau ∈ dynamicComplementZeroPacket S T k, c tau) * G)).symm
        _ = (∑ rho ∈ dynamicComplementZeroPacket S T n, c rho) *
              (∑ tau ∈ dynamicComplementZeroPacket S T k, c tau) * G := by
          ring
    _ = dynamicComplementPacketCoefficientMass S T beta a n *
          dynamicComplementPacketCoefficientMass S T beta a k *
          MathlibAux.gaussianBucketKernel n k := by
      rfl

/-- Gaussian interactions among the current complementary zeta packets are
bounded by the collision-safe square packet mass. -/
theorem dynamicComplementGaussianMajorantEnergy_le
    (S : Finset ℂ) (T beta a : ℝ) (K : Finset ℕ)
    {m : ℝ} (hm : 1 ≤ m) :
    dynamicComplementGaussianMajorantEnergy S T beta a K m ≤
      MathlibAux.gaussianBucketSchurConstant *
        ∑ n ∈ K,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 := by
  unfold dynamicComplementGaussianMajorantEnergy
  calc
    (∑ n ∈ K,
        ∑ k ∈ K,
          ∑ rho ∈ dynamicComplementZeroPacket S T n,
            ∑ tau ∈ dynamicComplementZeroPacket S T k,
              ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a rho‖ *
                ‖finiteZeroClusterCoefficientAt
                  (analyticOrderNatAt riemannZeta) beta a tau‖ *
                Real.exp (-m * (rho.im - tau.im) ^ 2)) ≤
        ∑ n ∈ K,
          ∑ k ∈ K,
            dynamicComplementPacketCoefficientMass S T beta a n *
              dynamicComplementPacketCoefficientMass S T beta a k *
              MathlibAux.gaussianBucketKernel n k := by
      apply Finset.sum_le_sum
      intro n hn
      apply Finset.sum_le_sum
      intro k hk
      exact dynamicComplementPacket_pair_sum_le S T beta a n k hm
    _ ≤ MathlibAux.gaussianBucketSchurConstant *
          ∑ n ∈ K,
            dynamicComplementPacketCoefficientMass S T beta a n ^ 2 :=
      MathlibAux.sum_mul_gaussianBucketKernel_le K
        (dynamicComplementPacketCoefficientMass S T beta a)

private theorem dynamicComplementPacketCoefficientMass_nonneg
    (S : Finset ℂ) (T beta a : ℝ) (n : ℕ) :
    0 ≤ dynamicComplementPacketCoefficientMass S T beta a n := by
  unfold dynamicComplementPacketCoefficientMass
  exact Finset.sum_nonneg fun rho _ => norm_nonneg _

/-- If the complementary Gaussian majorant energy is large, one actual,
disjoint zeta-zero packet can be absorbed into the dominant set.  The
quantitative mass lower bound is normalized by the number of inspected
buckets, so it is suitable for a later Carlson expansion budget. -/
theorem exists_absorbableDynamicComplementPacket_of_gaussianMajorantEnergy_gt
    {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ}
    (heta : 0 < eta)
    (hm : 1 ≤ m)
    (hK : K.Nonempty)
    (hlarge :
      eta < dynamicComplementGaussianMajorantEnergy S T beta a K m) :
    ∃ n ∈ K,
      eta /
            (MathlibAux.gaussianBucketSchurConstant *
              (K.card : ℝ)) <
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
        (dynamicComplementZeroPacket S T n).Nonempty ∧
        Disjoint S (dynamicComplementZeroPacket S T n) ∧
        dynamicComplementZeroPacket S T n ⊆
          nontrivialZerosFinset T ∧
        S.card <
          (S ∪ dynamicComplementZeroPacket S T n).card := by
  classical
  let C : ℝ := MathlibAux.gaussianBucketSchurConstant
  let q : ℝ := eta / (C * (K.card : ℝ))
  have hC : 0 < C := MathlibAux.gaussianBucketSchurConstant_pos
  have hcardNat : 0 < K.card := hK.card_pos
  have hcard : 0 < (K.card : ℝ) := by exact_mod_cast hcardNat
  have hdenom : 0 < C * (K.card : ℝ) := mul_pos hC hcard
  have henergy :=
    dynamicComplementGaussianMajorantEnergy_le S T beta a K hm
  have hscaled :
      eta <
        C * ∑ n ∈ K,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 :=
    hlarge.trans_le henergy
  have hexists :
      ∃ n ∈ K,
        q <
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 := by
    by_contra hnone
    push Not at hnone
    have hle :
        (∑ n ∈ K,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
          ∑ _n ∈ K, q := by
      exact Finset.sum_le_sum fun n hn => hnone n hn
    have hconst :
        (∑ _n ∈ K, q) = (K.card : ℝ) * q := by
      simp
    have hcardq : (K.card : ℝ) * q = eta / C := by
      dsimp [q]
      field_simp [hC.ne', show (K.card : ℝ) ≠ 0 by positivity]
    have hsum_le_etaC : (∑ n ∈ K,
        dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
        eta / C := hle.trans_eq (hconst.trans hcardq)
    have hmul :
        C * (∑ n ∈ K,
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2) ≤
          C * (eta / C) :=
      mul_le_mul_of_nonneg_left hsum_le_etaC hC.le
    have hcancel : C * (eta / C) = eta := by
      field_simp [hC.ne']
    exact (not_lt_of_ge (hmul.trans_eq hcancel)) hscaled
  obtain ⟨n, hnK, hnMass⟩ := hexists
  let P : Finset ℂ := dynamicComplementZeroPacket S T n
  have hqPos : 0 < q := div_pos heta hdenom
  have hP : P.Nonempty := by
    by_contra hPempty
    have hPEq : P = ∅ := Finset.not_nonempty_iff_eq_empty.mp hPempty
    have hmassZero :
        dynamicComplementPacketCoefficientMass S T beta a n = 0 := by
      simp [dynamicComplementPacketCoefficientMass, P, hPEq]
    rw [hmassZero] at hnMass
    norm_num at hnMass
    linarith
  have hdisjoint : Disjoint S P := by
    rw [Finset.disjoint_left]
    intro rho hrhoS hrhoP
    have hrhoComplement :
        rho ∈ nontrivialZerosFinset T \ S :=
      (Finset.mem_inter.mp hrhoP).2
    exact (Finset.mem_sdiff.mp hrhoComplement).2 hrhoS
  have hsubset : P ⊆ nontrivialZerosFinset T := by
    intro rho hrhoP
    exact (Finset.mem_sdiff.mp (Finset.mem_inter.mp hrhoP).2).1
  have hcardUnion :
      (S ∪ P).card = S.card + P.card :=
    Finset.card_union_of_disjoint hdisjoint
  have hcardP : 0 < P.card := hP.card_pos
  refine ⟨n, hnK, ?_, hP, hdisjoint, hsubset, ?_⟩
  · simpa [C, q] using hnMass
  · rw [hcardUnion]
    omega

/-- Concrete one-step expansion from a large frozen Gaussian `L²` energy of
the actual height-`T` zeta complement. -/
theorem exists_absorbableDynamicComplementPacket_of_frozenGaussianL2_gt
    {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ}
    (heta : 0 < eta)
    (hm : 1 ≤ m)
    (hK : K.Nonempty)
    (hlarge :
      eta <
        dynamicComplementFrozenGaussianSecondMoment
          S T beta a K m) :
    ∃ n ∈ K,
      eta /
            (MathlibAux.gaussianBucketSchurConstant *
              (K.card : ℝ)) <
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
        (dynamicComplementZeroPacket S T n).Nonempty ∧
        Disjoint S (dynamicComplementZeroPacket S T n) ∧
        dynamicComplementZeroPacket S T n ⊆
          nontrivialZerosFinset T ∧
        S.card <
          (S ∪ dynamicComplementZeroPacket S T n).card := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmajorant :=
    dynamicComplementFrozenGaussianSecondMoment_le_majorant
      S T beta a K hmPos
  exact
    exists_absorbableDynamicComplementPacket_of_gaussianMajorantEnergy_gt
      heta hm hK (hlarge.trans_le hmajorant)

/-- Window-centered version of the one-step expansion theorem. -/
theorem
    exists_absorbableDynamicComplementPacket_of_centeredFrozenGaussianL2_gt
    {S : Finset ℂ} {T beta a eta m : ℝ} {K : Finset ℕ}
    (heta : 0 < eta)
    (hm : 1 ≤ m)
    (hK : K.Nonempty)
    (hlarge :
      eta <
        dynamicComplementCenteredFrozenGaussianSecondMoment
          S T beta a K m) :
    ∃ n ∈ K,
      eta /
            (MathlibAux.gaussianBucketSchurConstant *
              (K.card : ℝ)) <
          dynamicComplementPacketCoefficientMass S T beta a n ^ 2 ∧
        (dynamicComplementZeroPacket S T n).Nonempty ∧
        Disjoint S (dynamicComplementZeroPacket S T n) ∧
        dynamicComplementZeroPacket S T n ⊆
          nontrivialZerosFinset T ∧
        S.card <
          (S ∪ dynamicComplementZeroPacket S T n).card := by
  have hmPos : 0 < m := lt_of_lt_of_le zero_lt_one hm
  have hmajorant :=
    dynamicComplementCenteredFrozenGaussianSecondMoment_le_majorant
      S T beta a K hmPos
  exact
    exists_absorbableDynamicComplementPacket_of_gaussianMajorantEnergy_gt
      heta hm hK (hlarge.trans_le hmajorant)

end

end VKEdgePiOverTwo
end PrimeNumberTheorem
