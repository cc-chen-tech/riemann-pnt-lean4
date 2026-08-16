import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Rat.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite quadratic forms and exact LDL certificates

This module isolates the algebraic implication used by finite Weil-form
experiments: an exact factorization `A = L D L^T` with nonnegative diagonal
gives a nonnegative real quadratic form. It makes no assertion that a supplied
finite matrix is an analytic Weil matrix.
-/

namespace WeilExtremalKernels

open scoped BigOperators

abbrev FiniteVector (n : ℕ) := Fin n → ℝ

abbrev FiniteMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℝ

/-- The finite real quadratic form `x^T A x`, written entrywise. -/
def quadraticForm {n : ℕ} (A : FiniteMatrix n) (x : FiniteVector n) : ℝ :=
  ∑ i, ∑ j, x i * A i j * x j

/-- The squared Euclidean norm, in the same entrywise style as `quadraticForm`. -/
def squaredNorm {n : ℕ} (x : FiniteVector n) : ℝ :=
  ∑ i, (x i) ^ 2

theorem squaredNorm_nonneg {n : ℕ} (x : FiniteVector n) : 0 ≤ squaredNorm x := by
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

theorem squaredNorm_pos {n : ℕ} {x : FiniteVector n} (hx : x ≠ 0) :
    0 < squaredNorm x := by
  have hexists : ∃ i, x i ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (funext h)
  obtain ⟨i, hi⟩ := hexists
  exact Finset.sum_pos' (fun j _ => sq_nonneg (x j)) ⟨i, by simp [sq_pos_of_ne_zero hi]⟩

/-- The matrix reconstructed from `L` and the diagonal of `D`. -/
def ldlMatrix {n : ℕ} (L : FiniteMatrix n) (d : FiniteVector n) : FiniteMatrix n :=
  fun i j => ∑ k, L i k * d k * L j k

/-- The linear form given by column `k` of `L`. -/
def columnLinearForm {n : ℕ} (L : FiniteMatrix n) (x : FiniteVector n) (k : Fin n) : ℝ :=
  ∑ i, L i k * x i

/-- Data carried by an exact finite `LDL^T` certificate. -/
structure LDLCertificate (n : ℕ) where
  lower : FiniteMatrix n
  diagonal : FiniteVector n

/-- The exact matrix reconstructed by a certificate. -/
def LDLCertificate.reconstruct {n : ℕ} (certificate : LDLCertificate n) :
    FiniteMatrix n :=
  ldlMatrix certificate.lower certificate.diagonal

/-- An `LDL^T` quadratic form is the weighted sum of its column squares. -/
theorem quadraticForm_ldlMatrix {n : ℕ} (L : FiniteMatrix n)
    (d x : FiniteVector n) :
    quadraticForm (ldlMatrix L d) x =
      ∑ k, d k * (columnLinearForm L x k) ^ 2 := by
  unfold quadraticForm ldlMatrix columnLinearForm
  calc
    (∑ i, ∑ j, x i * (∑ k, L i k * d k * L j k) * x j) =
        ∑ i, ∑ j, ∑ k, x i * (L i k * d k * L j k) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.mul_sum, Finset.sum_mul]
    _ = ∑ i, ∑ k, ∑ j, x i * (L i k * d k * L j k) * x j := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
    _ = ∑ k, ∑ i, ∑ j, x i * (L i k * d k * L j k) * x j := by
      rw [Finset.sum_comm]
    _ = ∑ k, d k * ((∑ i, L i k * x i) * ∑ j, L j k * x j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [Fintype.sum_mul_sum]
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ k, d k * (∑ i, L i k * x i) ^ 2 := by
      congr 1
      funext k
      rw [pow_two]

/-- A nonnegative diagonal makes the reconstructed quadratic form nonnegative. -/
theorem quadraticForm_ldlMatrix_nonneg {n : ℕ} (L : FiniteMatrix n)
    (d x : FiniteVector n) (hdiagonal : ∀ k, 0 ≤ d k) :
    0 ≤ quadraticForm (ldlMatrix L d) x := by
  rw [quadraticForm_ldlMatrix]
  exact Finset.sum_nonneg fun k _ => mul_nonneg (hdiagonal k) (sq_nonneg _)

/-- Transfer nonnegativity from an exact certificate reconstruction to `A`. -/
theorem quadraticForm_nonneg_of_certificate {n : ℕ} (A : FiniteMatrix n)
    (certificate : LDLCertificate n)
    (hreconstruct : A = certificate.reconstruct)
    (hdiagonal : ∀ k, 0 ≤ certificate.diagonal k) :
    ∀ x, 0 ≤ quadraticForm A x := by
  intro x
  rw [hreconstruct]
  exact quadraticForm_ldlMatrix_nonneg certificate.lower certificate.diagonal x hdiagonal

/-- A symmetric entrywise perturbation radius with row sums bounded by `ρ`
controls the quadratic-form error with the same constant `ρ`. -/
theorem abs_quadraticForm_sub_le_rowBound {n : ℕ}
    (A C R : FiniteMatrix n) (x : FiniteVector n) (ρ : ℝ)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) :
    |quadraticForm A x - quadraticForm C x| ≤ ρ * squaredNorm x := by
  have hRnonneg : ∀ i j, 0 ≤ R i j := fun i j =>
    (abs_nonneg (A i j - C i j)).trans (hentry i j)
  have hcol : ∀ j, ∑ i, R i j ≤ ρ := by
    intro j
    calc
      (∑ i, R i j) = ∑ i, R j i := by
        apply Finset.sum_congr rfl
        intro i _
        exact hR i j
      _ ≤ ρ := hrow j
  have hdiff : quadraticForm A x - quadraticForm C x =
      ∑ i, ∑ j, x i * (A i j - C i j) * x j := by
    unfold quadraticForm
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have habs : |quadraticForm A x - quadraticForm C x| ≤
      ∑ i, ∑ j, R i j * |x i| * |x j| := by
    rw [hdiff]
    calc
      |∑ i, ∑ j, x i * (A i j - C i j) * x j| ≤
          ∑ i, |∑ j, x i * (A i j - C i j) * x j| :=
        Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, |x i * (A i j - C i j) * x j| := by
        apply Finset.sum_le_sum
        intro i _
        exact Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∑ j, R i j * |x i| * |x j| := by
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro j _
        rw [abs_mul, abs_mul]
        calc
          |x i| * |A i j - C i j| * |x j| ≤
              |x i| * R i j * |x j| :=
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left (hentry i j) (abs_nonneg (x i)))
              (abs_nonneg (x j))
          _ = R i j * |x i| * |x j| := by ring
  have hpair : ∀ i j,
      R i j * |x i| * |x j| ≤
        (R i j * (x i) ^ 2 + R i j * (x j) ^ 2) / 2 := by
    intro i j
    have h := mul_le_mul_of_nonneg_left
      (two_mul_le_add_sq |x i| |x j|) (hRnonneg i j)
    rw [sq_abs, sq_abs] at h
    nlinarith
  have hfirst : (∑ i, ∑ j, R i j * (x i) ^ 2) ≤ ρ * squaredNorm x := by
    unfold squaredNorm
    calc
      (∑ i, ∑ j, R i j * (x i) ^ 2) =
          ∑ i, (∑ j, R i j) * (x i) ^ 2 := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_mul]
      _ ≤ ∑ i, ρ * (x i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (hrow i) (sq_nonneg (x i))
      _ = ρ * ∑ i, (x i) ^ 2 := by rw [Finset.mul_sum]
  have hsecond : (∑ i, ∑ j, R i j * (x j) ^ 2) ≤ ρ * squaredNorm x := by
    unfold squaredNorm
    calc
      (∑ i, ∑ j, R i j * (x j) ^ 2) =
          ∑ j, ∑ i, R i j * (x j) ^ 2 := by rw [Finset.sum_comm]
      _ = ∑ j, (∑ i, R i j) * (x j) ^ 2 := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
      _ ≤ ∑ j, ρ * (x j) ^ 2 := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_right (hcol j) (sq_nonneg (x j))
      _ = ρ * ∑ j, (x j) ^ 2 := by rw [Finset.mul_sum]
  calc
    |quadraticForm A x - quadraticForm C x| ≤
        ∑ i, ∑ j, R i j * |x i| * |x j| := habs
    _ ≤ ∑ i, ∑ j,
        (R i j * (x i) ^ 2 + R i j * (x j) ^ 2) / 2 := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact hpair i j
    _ = ((∑ i, ∑ j, R i j * (x i) ^ 2) +
        (∑ i, ∑ j, R i j * (x j) ^ 2)) / 2 := by
      simp_rw [add_div, Finset.sum_add_distrib, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ρ * squaredNorm x := by linarith

/-- A center lower bound that dominates the symmetric interval row budget
certifies every matrix in the enclosure as positive semidefinite. -/
theorem quadraticForm_nonneg_of_interval {n : ℕ}
    (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ ≤ μ) :
    ∀ x, 0 ≤ quadraticForm A x := by
  intro x
  have hperturb := abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow
  have hlower : quadraticForm C x - ρ * squaredNorm x ≤ quadraticForm A x := by
    have := neg_abs_le (quadraticForm A x - quadraticForm C x)
    linarith
  have hnorm := squaredNorm_nonneg x
  have hmargin : 0 ≤ (μ - ρ) * squaredNorm x :=
    mul_nonneg (sub_nonneg.mpr hbudget) hnorm
  linarith [hcenter x]

/-- Strict budget slack certifies a positive quadratic form on nonzero vectors. -/
theorem quadraticForm_pos_of_interval {n : ℕ}
    (A C R : FiniteMatrix n) (μ ρ : ℝ)
    (hcenter : ∀ x, μ * squaredNorm x ≤ quadraticForm C x)
    (hR : ∀ i j, R i j = R j i)
    (hentry : ∀ i j, |A i j - C i j| ≤ R i j)
    (hrow : ∀ i, ∑ j, R i j ≤ ρ) (hbudget : ρ < μ) :
    ∀ x, x ≠ 0 → 0 < quadraticForm A x := by
  intro x hx
  have hperturb := abs_quadraticForm_sub_le_rowBound A C R x ρ hR hentry hrow
  have hlower : quadraticForm C x - ρ * squaredNorm x ≤ quadraticForm A x := by
    have := neg_abs_le (quadraticForm A x - quadraticForm C x)
    linarith
  have hnorm := squaredNorm_pos hx
  have hmargin : 0 < (μ - ρ) * squaredNorm x :=
    mul_pos (sub_pos.mpr hbudget) hnorm
  linarith [hcenter x]

/-!
## Proof-carrying dual-route interval certificates

The structures below are a typed consumption boundary for generated JSON
artifacts.  They deliberately state only a finite-matrix claim.  Analytic
assembly code must separately prove that its Weil matrix lies in the stored
enclosure.
-/

/-- Versioned identity of one generated dual-route artifact. -/
structure ArtifactMetadata where
  schemaVersion : String
  c : ℕ
  N : ℕ
  dimension : ℕ
  indexConvention : String
  sourcePayloadSHA256 : List String
  payloadSHA256 : String
  deriving DecidableEq, Repr

/-- Add the scalar `μ` to every diagonal entry of a finite matrix. -/
def addDiagonal {n : ℕ} (A : FiniteMatrix n) (μ : ℝ) : FiniteMatrix n :=
  fun i j => A i j + if i = j then μ else 0

/-- Adding `μ I` adds `μ * ‖x‖²` to the associated quadratic form. -/
theorem quadraticForm_addDiagonal {n : ℕ} (A : FiniteMatrix n)
    (μ : ℝ) (x : FiniteVector n) :
    quadraticForm (addDiagonal A μ) x =
      quadraticForm A x + μ * squaredNorm x := by
  unfold quadraticForm addDiagonal
  calc
    (∑ i, ∑ j, x i * (A i j + if i = j then μ else 0) * x j) =
        (∑ i, ∑ j, x i * A i j * x j) +
          ∑ i, ∑ j, x i * (if i = j then μ else 0) * x j := by
      simp_rw [mul_add, add_mul, Finset.sum_add_distrib]
    _ = (∑ i, ∑ j, x i * A i j * x j) + ∑ i, μ * (x i) ^ 2 := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · simp
        ring
      · intro j _ hji
        simp [Ne.symm hji]
      · simp
    _ = (∑ i, ∑ j, x i * A i j * x j) + μ * ∑ i, (x i) ^ 2 := by
      rw [Finset.mul_sum]

/-- Parsed mathematical payload of a strict-overlap shifted-LDL artifact. -/
structure IntervalLDLCertificate (n : ℕ) where
  metadata : ArtifactMetadata
  center : FiniteMatrix n
  radius : FiniteMatrix n
  centerLowerBound : ℝ
  perturbationRowBound : ℝ
  shiftedLDL : LDLCertificate n

/-- Exact shifted `LDLᵀ` reconstruction gives the center's Euclidean lower bound. -/
theorem center_lowerBound_of_shifted_certificate {n : ℕ}
    (certificate : IntervalLDLCertificate n)
    (hreconstruct :
      certificate.center =
        addDiagonal certificate.shiftedLDL.reconstruct
          certificate.centerLowerBound)
    (hdiagonal : ∀ k, 0 ≤ certificate.shiftedLDL.diagonal k) :
    ∀ x, certificate.centerLowerBound * squaredNorm x ≤
      quadraticForm certificate.center x := by
  intro x
  rw [hreconstruct, quadraticForm_addDiagonal]
  have hshifted := quadraticForm_ldlMatrix_nonneg
    certificate.shiftedLDL.lower certificate.shiftedLDL.diagonal x hdiagonal
  exact le_add_of_nonneg_left hshifted

/-- Consume one metadata-bound strict-overlap interval certificate.

This theorem proves only a finite quadratic-form statement.  In particular it
does not imply an infinite-dimensional Weil criterion or RH.
-/
theorem quadraticForm_nonneg_of_intervalCertificate {n : ℕ}
    (A : FiniteMatrix n) (certificate : IntervalLDLCertificate n)
    (hreconstruct :
      certificate.center =
        addDiagonal certificate.shiftedLDL.reconstruct
          certificate.centerLowerBound)
    (hdiagonal : ∀ k, 0 ≤ certificate.shiftedLDL.diagonal k)
    (hR : ∀ i j, certificate.radius i j = certificate.radius j i)
    (hentry : ∀ i j,
      |A i j - certificate.center i j| ≤ certificate.radius i j)
    (hrow : ∀ i,
      ∑ j, certificate.radius i j ≤ certificate.perturbationRowBound)
    (hbudget :
      certificate.perturbationRowBound ≤ certificate.centerLowerBound) :
    ∀ x, 0 ≤ quadraticForm A x := by
  exact quadraticForm_nonneg_of_interval
    A certificate.center certificate.radius
    certificate.centerLowerBound certificate.perturbationRowBound
    (center_lowerBound_of_shifted_certificate certificate hreconstruct hdiagonal)
    hR hentry hrow hbudget

/-- Strict shifted-LDL budget gives positive definiteness on nonzero vectors. -/
theorem quadraticForm_pos_of_intervalCertificate {n : ℕ}
    (A : FiniteMatrix n) (certificate : IntervalLDLCertificate n)
    (hreconstruct :
      certificate.center =
        addDiagonal certificate.shiftedLDL.reconstruct
          certificate.centerLowerBound)
    (hdiagonal : ∀ k, 0 ≤ certificate.shiftedLDL.diagonal k)
    (hR : ∀ i j, certificate.radius i j = certificate.radius j i)
    (hentry : ∀ i j,
      |A i j - certificate.center i j| ≤ certificate.radius i j)
    (hrow : ∀ i,
      ∑ j, certificate.radius i j ≤ certificate.perturbationRowBound)
    (hbudget :
      certificate.perturbationRowBound < certificate.centerLowerBound) :
    ∀ x, x ≠ 0 → 0 < quadraticForm A x := by
  exact quadraticForm_pos_of_interval
    A certificate.center certificate.radius
    certificate.centerLowerBound certificate.perturbationRowBound
    (center_lowerBound_of_shifted_certificate certificate hreconstruct hdiagonal)
    hR hentry hrow hbudget

/-- Pinned identity of the shipped `(c,N) = (13,16)` artifact. -/
def c13N16ArtifactMetadata : ArtifactMetadata where
  schemaVersion := "weil-extremal-kernel-dual-route-certificate/v1"
  c := 13
  N := 16
  dimension := 33
  indexConvention := "fourier -N..N row-major"
  sourcePayloadSHA256 := [
    "09728fc84cf26e8079e22d39d92ad8077cdb8b498adcc60b053106dba2d8b277",
    "c6e4023c1e2a3e0c62eefe8ae79d884fba6c4bb057d6363e3c39114913d15a5f"
  ]
  payloadSHA256 := "35f0a74b64ba9d4fb8546524bb0d3e2057dece89885f47114c0e30699f49eb1d"

/-- Pinned identity of the shipped `(c,N) = (13,32)` artifact. -/
def c13N32ArtifactMetadata : ArtifactMetadata where
  schemaVersion := "weil-extremal-kernel-dual-route-certificate/v1"
  c := 13
  N := 32
  dimension := 65
  indexConvention := "fourier -N..N row-major"
  sourcePayloadSHA256 := [
    "2c5fb2e64b1e92666d4f7b813ce95caef8050f5498622873487f9f07d16ffa04",
    "f3d0c4396c22e5e015376dc4974af3061afa4c3c80d0dc9c6214d526ee58df52"
  ]
  payloadSHA256 := "e81265c2c7884575b911cc0942767e967ab0c482773f3bd2a3fbeeb3edb32d40"

/-- Fixed-size `(13,16)` certificate consumer. -/
theorem c13N16_quadraticForm_nonneg
    (A : FiniteMatrix 33) (certificate : IntervalLDLCertificate 33)
    (_hmetadata : certificate.metadata = c13N16ArtifactMetadata)
    (hreconstruct :
      certificate.center =
        addDiagonal certificate.shiftedLDL.reconstruct
          certificate.centerLowerBound)
    (hdiagonal : ∀ k, 0 ≤ certificate.shiftedLDL.diagonal k)
    (hR : ∀ i j, certificate.radius i j = certificate.radius j i)
    (hentry : ∀ i j,
      |A i j - certificate.center i j| ≤ certificate.radius i j)
    (hrow : ∀ i,
      ∑ j, certificate.radius i j ≤ certificate.perturbationRowBound)
    (hbudget :
      certificate.perturbationRowBound ≤ certificate.centerLowerBound) :
    ∀ x, 0 ≤ quadraticForm A x :=
  quadraticForm_nonneg_of_intervalCertificate
    A certificate hreconstruct hdiagonal hR hentry hrow hbudget

/-- Fixed-size `(13,32)` certificate consumer. -/
theorem c13N32_quadraticForm_nonneg
    (A : FiniteMatrix 65) (certificate : IntervalLDLCertificate 65)
    (_hmetadata : certificate.metadata = c13N32ArtifactMetadata)
    (hreconstruct :
      certificate.center =
        addDiagonal certificate.shiftedLDL.reconstruct
          certificate.centerLowerBound)
    (hdiagonal : ∀ k, 0 ≤ certificate.shiftedLDL.diagonal k)
    (hR : ∀ i j, certificate.radius i j = certificate.radius j i)
    (hentry : ∀ i j,
      |A i j - certificate.center i j| ≤ certificate.radius i j)
    (hrow : ∀ i,
      ∑ j, certificate.radius i j ≤ certificate.perturbationRowBound)
    (hbudget :
      certificate.perturbationRowBound ≤ certificate.centerLowerBound) :
    ∀ x, 0 ≤ quadraticForm A x :=
  quadraticForm_nonneg_of_intervalCertificate
    A certificate hreconstruct hdiagonal hR hentry hrow hbudget

/-!
## Lean-native-replayable rational artifacts

Generated certificate modules instantiate the following structure with exact
`ℚ` data and prove `Valid` by `native_decide`.  The soundness theorem then
casts those checked equalities to `ℝ`; callers supply only the analytic fact
that their matrix lies in the certified center-radius enclosure.
-/

abbrev RationalFiniteVector (n : ℕ) := Fin n → ℚ

abbrev RationalFiniteMatrix (n : ℕ) := Matrix (Fin n) (Fin n) ℚ

/-- Turn generated row arrays into a rational matrix. -/
abbrev rationalMatrixOfRows {n : ℕ} (rows : Array (Array ℚ)) :
    RationalFiniteMatrix n :=
  fun i j => (rows[i.val]!)[j.val]!

/-- Turn a generated array into a rational vector. -/
abbrev rationalVectorOfArray {n : ℕ} (values : Array ℚ) :
    RationalFiniteVector n :=
  fun i => values[i.val]!

/-- Exact rational payload emitted from one overlap JSON artifact. -/
structure RationalIntervalLDLCertificate (n : ℕ) where
  metadata : ArtifactMetadata
  lower : RationalFiniteMatrix n
  upper : RationalFiniteMatrix n
  shiftedLower : RationalFiniteMatrix n
  shiftedDiagonal : RationalFiniteVector n
  centerLowerBound : ℚ
  perturbationRowBound : ℚ

abbrev RationalIntervalLDLCertificate.center {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    RationalFiniteMatrix n :=
  fun i j => (certificate.lower i j + certificate.upper i j) / 2

abbrev RationalIntervalLDLCertificate.radius {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    RationalFiniteMatrix n :=
  fun i j => (certificate.upper i j - certificate.lower i j) / 2

abbrev RationalIntervalLDLCertificate.shiftedReconstruct {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    RationalFiniteMatrix n :=
  fun i j => ∑ k,
    certificate.shiftedLower i k * certificate.shiftedDiagonal k *
      certificate.shiftedLower j k

/-- Entire decidable finite certificate contract replayed by generated modules. -/
abbrev RationalIntervalLDLCertificate.Valid {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) : Prop :=
  (∀ i j, certificate.lower i j ≤ certificate.upper i j) ∧
  (∀ i j, certificate.radius i j = certificate.radius j i) ∧
  (∀ i j,
    certificate.center i j =
      certificate.shiftedReconstruct i j +
        if i = j then certificate.centerLowerBound else 0) ∧
  (∀ k, 0 ≤ certificate.shiftedDiagonal k) ∧
  (∀ i, ∑ j, certificate.radius i j ≤ certificate.perturbationRowBound) ∧
  certificate.perturbationRowBound ≤ certificate.centerLowerBound

instance RationalIntervalLDLCertificate.instDecidableValid {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    Decidable certificate.Valid := by
  unfold RationalIntervalLDLCertificate.Valid
  infer_instance

/-- The strict certificate contract used by the shipped N=16/32 artifacts. -/
abbrev RationalIntervalLDLCertificate.StrictValid {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) : Prop :=
  certificate.Valid ∧
    certificate.perturbationRowBound < certificate.centerLowerBound

instance RationalIntervalLDLCertificate.instDecidableStrictValid {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    Decidable certificate.StrictValid := by
  unfold RationalIntervalLDLCertificate.StrictValid
  infer_instance

def rationalMatrixToReal {n : ℕ} (A : RationalFiniteMatrix n) :
    FiniteMatrix n :=
  fun i j => (A i j : ℝ)

def rationalVectorToReal {n : ℕ} (x : RationalFiniteVector n) :
    FiniteVector n :=
  fun i => (x i : ℝ)

/-- The real interval certificate whose data are exactly the checked rationals. -/
def RationalIntervalLDLCertificate.toReal {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n) :
    IntervalLDLCertificate n where
  metadata := certificate.metadata
  center := rationalMatrixToReal certificate.center
  radius := rationalMatrixToReal certificate.radius
  centerLowerBound := certificate.centerLowerBound
  perturbationRowBound := certificate.perturbationRowBound
  shiftedLDL := {
    lower := rationalMatrixToReal certificate.shiftedLower
    diagonal := rationalVectorToReal certificate.shiftedDiagonal
  }

/-- A Lean-native-replayed rational artifact implies PSD for every matrix in its enclosure. -/
theorem RationalIntervalLDLCertificate.quadraticForm_nonneg {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n)
    (hvalid : certificate.Valid)
    (A : FiniteMatrix n)
    (hentry : ∀ i j,
      |A i j - certificate.toReal.center i j| ≤
        certificate.toReal.radius i j) :
    ∀ x, 0 ≤ quadraticForm A x := by
  rcases hvalid with
    ⟨_hlower, hRrat, hreconstructRat, hdiagonalRat, hrowRat, hbudgetRat⟩
  have hreconstruct :
      certificate.toReal.center =
        addDiagonal certificate.toReal.shiftedLDL.reconstruct
          certificate.toReal.centerLowerBound := by
    funext i j
    change (certificate.center i j : ℝ) =
      (∑ k,
        (certificate.shiftedLower i k : ℝ) *
          (certificate.shiftedDiagonal k : ℝ) *
          (certificate.shiftedLower j k : ℝ)) +
        if i = j then (certificate.centerLowerBound : ℝ) else 0
    have hcast :
        (certificate.center i j : ℝ) =
          ((certificate.shiftedReconstruct i j +
            if i = j then certificate.centerLowerBound else 0 : ℚ) : ℝ) := by
      exact_mod_cast hreconstructRat i j
    by_cases hij : i = j
    · simpa [RationalIntervalLDLCertificate.shiftedReconstruct, hij] using hcast
    · simpa [RationalIntervalLDLCertificate.shiftedReconstruct, hij] using hcast
  have hdiagonal :
      ∀ k, 0 ≤ certificate.toReal.shiftedLDL.diagonal k := by
    intro k
    change (0 : ℝ) ≤ (certificate.shiftedDiagonal k : ℝ)
    exact_mod_cast hdiagonalRat k
  have hR :
      ∀ i j, certificate.toReal.radius i j =
        certificate.toReal.radius j i := by
    intro i j
    change (certificate.radius i j : ℝ) = (certificate.radius j i : ℝ)
    exact_mod_cast hRrat i j
  have hrow :
      ∀ i, ∑ j, certificate.toReal.radius i j ≤
        certificate.toReal.perturbationRowBound := by
    intro i
    change (∑ j, (certificate.radius i j : ℝ)) ≤
      (certificate.perturbationRowBound : ℝ)
    have hrowCast :
        ((∑ j, certificate.radius i j : ℚ) : ℝ) ≤
          (certificate.perturbationRowBound : ℝ) := by
      exact_mod_cast hrowRat i
    simpa using hrowCast
  have hbudget :
      certificate.toReal.perturbationRowBound ≤
        certificate.toReal.centerLowerBound := by
    change (certificate.perturbationRowBound : ℝ) ≤
      (certificate.centerLowerBound : ℝ)
    exact_mod_cast hbudgetRat
  exact quadraticForm_nonneg_of_intervalCertificate
    A certificate.toReal hreconstruct hdiagonal hR hentry hrow hbudget

/-- Lower/upper membership implies the center-radius condition consumed above. -/
theorem RationalIntervalLDLCertificate.entry_bound_of_bounds {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n)
    (A : FiniteMatrix n)
    (hbounds : ∀ i j,
      (certificate.lower i j : ℝ) ≤ A i j ∧
        A i j ≤ (certificate.upper i j : ℝ)) :
    ∀ i j,
      |A i j - certificate.toReal.center i j| ≤
        certificate.toReal.radius i j := by
  intro i j
  rcases hbounds i j with ⟨hlower, hupper⟩
  change
    |A i j - (((certificate.lower i j + certificate.upper i j) / 2 : ℚ) : ℝ)| ≤
      (((certificate.upper i j - certificate.lower i j) / 2 : ℚ) : ℝ)
  norm_num
  rw [abs_le]
  constructor <;> linarith

/-- PSD theorem with the natural lower/upper artifact interface. -/
theorem RationalIntervalLDLCertificate.quadraticForm_nonneg_of_bounds {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n)
    (hvalid : certificate.Valid)
    (A : FiniteMatrix n)
    (hbounds : ∀ i j,
      (certificate.lower i j : ℝ) ≤ A i j ∧
        A i j ≤ (certificate.upper i j : ℝ)) :
    ∀ x, 0 ≤ quadraticForm A x :=
  certificate.quadraticForm_nonneg hvalid A
    (certificate.entry_bound_of_bounds A hbounds)

/-- Strict rational certificate gives PD for every matrix in its bounds. -/
theorem RationalIntervalLDLCertificate.quadraticForm_pos_of_bounds {n : ℕ}
    (certificate : RationalIntervalLDLCertificate n)
    (hstrict : certificate.StrictValid)
    (A : FiniteMatrix n)
    (hbounds : ∀ i j,
      (certificate.lower i j : ℝ) ≤ A i j ∧
        A i j ≤ (certificate.upper i j : ℝ)) :
    ∀ x, x ≠ 0 → 0 < quadraticForm A x := by
  rcases hstrict with ⟨hvalid, hstrictRat⟩
  rcases hvalid with
    ⟨_hlower, hRrat, hreconstructRat, hdiagonalRat, hrowRat, _hbudgetRat⟩
  have hreconstruct :
      certificate.toReal.center =
        addDiagonal certificate.toReal.shiftedLDL.reconstruct
          certificate.toReal.centerLowerBound := by
    funext i j
    change (certificate.center i j : ℝ) =
      (∑ k,
        (certificate.shiftedLower i k : ℝ) *
          (certificate.shiftedDiagonal k : ℝ) *
          (certificate.shiftedLower j k : ℝ)) +
        if i = j then (certificate.centerLowerBound : ℝ) else 0
    have hcast :
        (certificate.center i j : ℝ) =
          ((certificate.shiftedReconstruct i j +
            if i = j then certificate.centerLowerBound else 0 : ℚ) : ℝ) := by
      exact_mod_cast hreconstructRat i j
    by_cases hij : i = j
    · simpa [RationalIntervalLDLCertificate.shiftedReconstruct, hij] using hcast
    · simpa [RationalIntervalLDLCertificate.shiftedReconstruct, hij] using hcast
  have hdiagonal :
      ∀ k, 0 ≤ certificate.toReal.shiftedLDL.diagonal k := by
    intro k
    change (0 : ℝ) ≤ (certificate.shiftedDiagonal k : ℝ)
    exact_mod_cast hdiagonalRat k
  have hR :
      ∀ i j, certificate.toReal.radius i j =
        certificate.toReal.radius j i := by
    intro i j
    change (certificate.radius i j : ℝ) = (certificate.radius j i : ℝ)
    exact_mod_cast hRrat i j
  have hrow :
      ∀ i, ∑ j, certificate.toReal.radius i j ≤
        certificate.toReal.perturbationRowBound := by
    intro i
    change (∑ j, (certificate.radius i j : ℝ)) ≤
      (certificate.perturbationRowBound : ℝ)
    have hrowCast :
        ((∑ j, certificate.radius i j : ℚ) : ℝ) ≤
          (certificate.perturbationRowBound : ℝ) := by
      exact_mod_cast hrowRat i
    simpa using hrowCast
  have hbudget :
      certificate.toReal.perturbationRowBound <
        certificate.toReal.centerLowerBound := by
    change (certificate.perturbationRowBound : ℝ) <
      (certificate.centerLowerBound : ℝ)
    exact_mod_cast hstrictRat
  exact quadraticForm_pos_of_intervalCertificate
    A certificate.toReal hreconstruct hdiagonal hR
    (certificate.entry_bound_of_bounds A hbounds) hrow hbudget

end WeilExtremalKernels
