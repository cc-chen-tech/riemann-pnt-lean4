import HardyTheorem.SelbergSmoothCoprimeSplit
import HardyTheorem.SelbergSqrtZetaMollifier

open Complex
open Nat

namespace HardyTheorem

/-!
# Exact bridge from Selberg's taper to the real Perron cutoff

The arithmetic split must preserve the logarithmic weight exactly.  These
lemmas identify the finite taper with `log+ / log X`, move from the global
ratio `d*k/X` to the local cutoff `k/(X/d)`, and combine that identity with
the coprime factorization of the square-root-zeta coefficient.
-/

theorem selbergSqrtZetaTaperedCoeff_eq_perronCutoff
    {X n : ℕ} (hX : 2 ≤ X) (hn : 0 < n) (hnX : n ≤ X) :
    (selbergSqrtZetaTaperedCoeff X n : ℂ) =
      selbergSqrtZetaCoeffComplex n *
        perronLogCutoff ((n : ℝ) / (X : ℝ)) /
          (Real.log (X : ℝ) : ℂ) := by
  have hXpos : 0 < X := by omega
  have hlogX : Real.log (X : ℝ) ≠ 0 := by
    exact ne_of_gt (Real.log_pos (by exact_mod_cast (show 1 < X by omega)))
  rw [perronLogCutoff_nat_div_eq_log hn hXpos hnX]
  rw [selbergSqrtZetaTaperedCoeff, selbergMoebiusWeight]
  simp only [selbergSqrtZetaCoeffComplex_apply]
  norm_cast
  rw [Real.log_div (by positivity : (X : ℝ) ≠ 0)
    (by positivity : (n : ℝ) ≠ 0)]
  field_simp

theorem perronLogCutoff_mul_div_eq_localCutoff
    {X : ℝ} {d k : ℕ} (hX : 0 < X) :
    perronLogCutoff (((d * k : ℕ) : ℝ) / X) =
      perronLogCutoff ((k : ℝ) / (X / (d : ℝ))) := by
  congr 1
  field_simp
  simp [Nat.cast_mul, mul_comm]

theorem selbergTaperedShiftedTerm_split
    {X rho d k : ℕ} (theta : ℝ)
    (hX : 2 ≤ X) (hd : 0 < d) (hk : 0 < k)
    (hdkX : d * k ≤ X)
    (hdsupp : d ∈ factoredNumbers rho.primeFactors)
    (hcop : k.Coprime rho) :
    (selbergSqrtZetaTaperedCoeff X (d * k) : ℂ) *
        ((d * k : ℕ) : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) =
      ((selbergSqrtZetaCoeff d : ℂ) *
          (d : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) /
            (Real.log (X : ℝ) : ℂ)) *
        (selbergS12ShiftedCoprimeCoeff rho theta k *
          perronLogCutoff ((k : ℝ) / ((X : ℝ) / (d : ℝ)))) := by
  have hdkcop : d.Coprime k := by
    rw [← Nat.disjoint_primeFactors hd.ne' hk.ne']
    exact hcop.disjoint_primeFactors.symm.mono
      (primeFactors_subset_of_mem_factoredNumbers hdsupp) (fun _ h => h)
  have hcoeff : selbergSqrtZetaCoeff (d * k) =
      selbergSqrtZetaCoeff d * selbergSqrtZetaCoeff k :=
    selbergSqrtZetaCoeff_isMultiplicative.map_mul_of_coprime hdkcop
  rw [selbergSqrtZetaTaperedCoeff_eq_perronCutoff hX
    (Nat.mul_pos hd hk) hdkX]
  rw [perronLogCutoff_mul_div_eq_localCutoff
    (show (0 : ℝ) < X by exact_mod_cast (show 0 < X by omega))]
  rw [selbergSqrtZetaCoeffComplex_apply, hcoeff]
  unfold selbergS12ShiftedCoprimeCoeff
  rw [selbergS12CoprimeCoeff_of_coprime hcop]
  simp only [selbergSqrtZetaCoeffComplex_apply, Nat.cast_mul]
  have hpow :
      ((d : ℂ) * (k : ℂ)) ^ (-((1 - theta : ℝ) : ℂ)) =
        (d : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) *
          (k : ℂ) ^ (-((1 - theta : ℝ) : ℂ)) := by
    simpa only [Complex.ofReal_natCast] using
      (Complex.mul_cpow_ofReal_nonneg
        (a := (d : ℝ)) (b := (k : ℝ))
        (Nat.cast_nonneg d) (Nat.cast_nonneg k)
        (-((1 - theta : ℝ) : ℂ)))
  rw [hpow]
  push_cast
  ring

end HardyTheorem
