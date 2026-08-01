import MathlibAux.GaussianBucketSchur

/-!
# Dyadic drifting Gaussian Schur bound

This file is the abstract first stage of the half-isolated dyadic L2 task.  The
finite set `S` is intended to be one dyadic height block.  It proves a whole
Gram-matrix estimate, not merely pairwise cross-term bounds.

The factor `occupancy + 1` bounds the cardinality of every unit-frequency
bucket.  If that bound fails, the companion dichotomy theorem returns a bucket
with strictly more than `occupancy + 1` entries.  Squared masses are retained
on the right, so a later zeta instantiation may use analytic multiplicities in
the mass itself.

Real-part drift is kept explicitly through `exp (drift i * t)`.  The theorem
uses only nonpositive drift on a nonnegative displacement.  Actual zeta zeros,
dyadic membership, low-zero removal, and local multiplicity estimates are
deliberately left to the second-stage adapter.
-/

namespace MathlibAux

section

variable {ι : Type*} [DecidableEq ι]

/-- The mass at displacement `t`, retaining a point's real-direction drift. -/
noncomputable def driftingMass (mass drift : ι → ℝ) (t : ℝ) (i : ι) : ℝ :=
  mass i * Real.exp (drift i * t)

/-- The full finite Gaussian Gram interaction with explicit real drift. -/
noncomputable def dyadicDriftingGaussianGram
    (S : Finset ι) (mass drift freq : ι → ℝ) (t m : ℝ) : ℝ :=
  ∑ i ∈ S, ∑ j ∈ S,
    driftingMass mass drift t i * driftingMass mass drift t j *
      Real.exp (-m * (freq i - freq j) ^ 2)

private theorem sum_bucketMass_sq_le_occupancy_mul_sum_sq
    (S : Finset ι) (mass : ι → ℝ) (bucket : ι → ℕ) (occupancy : ℕ)
    (hoccupancy : ∀ n ∈ S.image bucket,
      (S.filter fun i => bucket i = n).card ≤ occupancy + 1) :
    ∑ n ∈ S.image bucket, (∑ i ∈ S with bucket i = n, mass i) ^ 2 ≤
      ((occupancy + 1 : ℕ) : ℝ) * ∑ i ∈ S, mass i ^ 2 := by
  have hbucket : ∀ n ∈ S.image bucket,
      (∑ i ∈ S with bucket i = n, mass i) ^ 2 ≤
        ((occupancy + 1 : ℕ) : ℝ) *
          ∑ i ∈ S with bucket i = n, mass i ^ 2 := by
    intro n hn
    let fiber := S.filter fun i => bucket i = n
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq fiber mass (fun _ => (1 : ℝ))
    have hcard : (fiber.card : ℝ) ≤ ((occupancy + 1 : ℕ) : ℝ) := by
      exact_mod_cast hoccupancy n hn
    have hsquares : 0 ≤ ∑ i ∈ S with bucket i = n, mass i ^ 2 := by
      exact Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc
      (∑ i ∈ S with bucket i = n, mass i) ^ 2 =
          (∑ i ∈ fiber, mass i * 1) ^ 2 := by
            simp [fiber]
      _ ≤ (∑ i ∈ fiber, mass i ^ 2) * ∑ i ∈ fiber, (1 : ℝ) ^ 2 := hcs
      _ = (∑ i ∈ S with bucket i = n, mass i ^ 2) * (fiber.card : ℝ) := by
            simp [fiber]
      _ ≤ (∑ i ∈ S with bucket i = n, mass i ^ 2) *
          ((occupancy + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hcard hsquares
      _ = ((occupancy + 1 : ℕ) : ℝ) *
          ∑ i ∈ S with bucket i = n, mass i ^ 2 := by ring
  calc
    ∑ n ∈ S.image bucket, (∑ i ∈ S with bucket i = n, mass i) ^ 2 ≤
        ∑ n ∈ S.image bucket,
          ((occupancy + 1 : ℕ) : ℝ) *
            ∑ i ∈ S with bucket i = n, mass i ^ 2 :=
      Finset.sum_le_sum fun n hn => hbucket n hn
    _ = ((occupancy + 1 : ℕ) : ℝ) *
        ∑ n ∈ S.image bucket, ∑ i ∈ S with bucket i = n, mass i ^ 2 := by
          rw [Finset.mul_sum]
    _ = ((occupancy + 1 : ℕ) : ℝ) * ∑ i ∈ S, mass i ^ 2 := by
      rw [Finset.sum_fiberwise_of_maps_to
        (fun i hi => Finset.mem_image.mpr ⟨i, hi, rfl⟩)]

/--
Whole-Gram Gaussian separation under a quantitative unit-bucket occupancy cap.

The conclusion retains a square for every individual mass.  In the zeta
adapter the intended mass is
`multiplicity rho / |rho| * x ^ (re rho - beta)`.
-/
theorem gaussianGram_le_occupancy_mul_sum_sq
    (S : Finset ι) (mass freq : ι → ℝ) (bucket : ι → ℕ)
    (occupancy : ℕ) {m : ℝ}
    (hm : 1 ≤ m)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hgap : ∀ i ∈ S, ∀ j ∈ S,
      ((bucket i).dist (bucket j) - 1 : ℕ) ≤ |freq i - freq j|)
    (hoccupancy : ∀ n ∈ S.image bucket,
      (S.filter fun i => bucket i = n).card ≤ occupancy + 1) :
    ∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j * Real.exp (-m * (freq i - freq j) ^ 2) ≤
      gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ i ∈ S, mass i ^ 2 := by
  calc
    ∑ i ∈ S, ∑ j ∈ S,
        mass i * mass j * Real.exp (-m * (freq i - freq j) ^ 2) ≤
        gaussianBucketSchurConstant *
          ∑ n ∈ S.image bucket, (∑ i ∈ S with bucket i = n, mass i) ^ 2 :=
      sum_gaussianKernel_le_bucketEnergy S mass freq bucket hm hmass hgap
    _ ≤ gaussianBucketSchurConstant *
        (((occupancy + 1 : ℕ) : ℝ) * ∑ i ∈ S, mass i ^ 2) :=
      mul_le_mul_of_nonneg_left
        (sum_bucketMass_sq_le_occupancy_mul_sum_sq
          S mass bucket occupancy hoccupancy)
        gaussianBucketSchurConstant_pos.le
    _ = gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ i ∈ S, mass i ^ 2 := by ring

/--
The drifting dyadic Gram bound.  Nonpositive real drift on a nonnegative
displacement cannot increase the individual squared masses.
-/
theorem dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
    (S : Finset ι) (mass drift freq : ι → ℝ) (bucket : ι → ℕ)
    (occupancy : ℕ) {t m : ℝ}
    (ht : 0 ≤ t)
    (hm : 1 ≤ m)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hdrift : ∀ i ∈ S, drift i ≤ 0)
    (hgap : ∀ i ∈ S, ∀ j ∈ S,
      ((bucket i).dist (bucket j) - 1 : ℕ) ≤ |freq i - freq j|)
    (hoccupancy : ∀ n ∈ S.image bucket,
      (S.filter fun i => bucket i = n).card ≤ occupancy + 1) :
    dyadicDriftingGaussianGram S mass drift freq t m ≤
      gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ i ∈ S, mass i ^ 2 := by
  let moved := driftingMass mass drift t
  have hmoved_nonneg : ∀ i ∈ S, 0 ≤ moved i := by
    intro i hi
    exact mul_nonneg (hmass i hi) (Real.exp_pos _).le
  have hmoved_sq : ∀ i ∈ S, moved i ^ 2 ≤ mass i ^ 2 := by
    intro i hi
    have hdt : drift i * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (hdrift i hi) ht
    have hexp : Real.exp (drift i * t) ≤ 1 := by
      simpa using Real.exp_le_exp.mpr hdt
    have hmoved_le : moved i ≤ mass i := by
      exact mul_le_of_le_one_right (hmass i hi) hexp
    have hprod : 0 ≤ (mass i - moved i) * (mass i + moved i) :=
      mul_nonneg (sub_nonneg.mpr hmoved_le)
        (add_nonneg (hmass i hi) (hmoved_nonneg i hi))
    nlinarith
  calc
    dyadicDriftingGaussianGram S mass drift freq t m =
        ∑ i ∈ S, ∑ j ∈ S,
          moved i * moved j * Real.exp (-m * (freq i - freq j) ^ 2) := rfl
    _ ≤ gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ i ∈ S, moved i ^ 2 :=
      gaussianGram_le_occupancy_mul_sum_sq
        S moved freq bucket occupancy hm hmoved_nonneg hgap hoccupancy
    _ ≤ gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
        ∑ i ∈ S, mass i ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum fun i hi => hmoved_sq i hi)
        (mul_nonneg gaussianBucketSchurConstant_pos.le (by positivity))

/--
Separation-or-clustering form.  Either the full drifting Gram energy satisfies
the squared-mass bound, or one concrete frequency bucket contains strictly
more than `occupancy + 1` points.
-/
theorem dyadicDriftingGaussianGram_le_or_quantitativeCluster
    (S : Finset ι) (mass drift freq : ι → ℝ) (bucket : ι → ℕ)
    (occupancy : ℕ) {t m : ℝ}
    (ht : 0 ≤ t)
    (hm : 1 ≤ m)
    (hmass : ∀ i ∈ S, 0 ≤ mass i)
    (hdrift : ∀ i ∈ S, drift i ≤ 0)
    (hgap : ∀ i ∈ S, ∀ j ∈ S,
      ((bucket i).dist (bucket j) - 1 : ℕ) ≤ |freq i - freq j|) :
    dyadicDriftingGaussianGram S mass drift freq t m ≤
        gaussianBucketSchurConstant * ((occupancy + 1 : ℕ) : ℝ) *
          ∑ i ∈ S, mass i ^ 2 ∨
      ∃ n ∈ S.image bucket,
        occupancy + 1 < (S.filter fun i => bucket i = n).card := by
  by_cases hoccupancy : ∀ n ∈ S.image bucket,
      (S.filter fun i => bucket i = n).card ≤ occupancy + 1
  · exact Or.inl <| dyadicDriftingGaussianGram_le_occupancy_mul_sum_sq
      S mass drift freq bucket occupancy ht hm hmass hdrift hgap hoccupancy
  · right
    push_neg at hoccupancy
    exact hoccupancy

end

end MathlibAux
