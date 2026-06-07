import RiemannExplorer
import GammaResidue
import HardyTheorem
import EulerAndLfunctions
import PrimeNumberTheorem
import ZeroFreeRegion
import ZeroFreeRegion.MeromorphicAux

open Complex Filter Topology Asymptotics ComplexConjugate
open scoped ArithmeticFunction LSeries.notation

namespace RiemannPNT.API

/-- Public compatibility bridge between the project's prime-counting
normalization and Mathlib's `Nat.primeCounting`. -/
theorem primeCounting_eq_mathlib (x : ℝ) (hx : 0 ≤ x) :
    PrimeNumberTheorem.primeCounting x = Nat.primeCounting ⌊x⌋₊ :=
  PrimeNumberTheorem.primeCounting_eq_mathlib x hx

/-- Public compatibility bridge between the project's von Mangoldt function and
Mathlib's arithmetic-function definition. -/
theorem vonMangoldt_eq_mathlib (n : ℕ) :
    PrimeNumberTheorem.vonMangoldt n =
      ArithmeticFunction.vonMangoldt n :=
  PrimeNumberTheorem.vonMangoldt_eq_mathlib n

/-- Public compatibility bridge between the project's Chebyshev-ψ normalization
and Mathlib's `Chebyshev.psi`. -/
theorem chebyshevPsi_eq_mathlib (x : ℝ) :
    PrimeNumberTheorem.chebyshevPsi x = Chebyshev.psi x :=
  PrimeNumberTheorem.chebyshevPsi_eq_mathlib x

/-- Public integration-by-parts formula for the logarithmic integral
normalization used in the PNT chain. -/
theorem logIntegral_integration_by_parts (x : ℝ) (hx : 2 ≤ x) :
    PrimeNumberTheorem.logIntegral x =
      x / Real.log x - 2 / Real.log 2 +
        ∫ t in (2)..x, 1 / (Real.log t)^2 :=
  PrimeNumberTheorem.logIntegral_integration_by_parts x hx

/-- Public nonnegativity of the logarithmic integral normalization on
`[2,∞)`. -/
theorem logIntegral_nonneg {x : ℝ} (hx : 2 ≤ x) :
    0 ≤ PrimeNumberTheorem.logIntegral x :=
  PrimeNumberTheorem.logIntegral_nonneg hx

/-- Public positivity of the logarithmic integral normalization on `(2,∞)`. -/
theorem logIntegral_pos {x : ℝ} (hx : 2 < x) :
    0 < PrimeNumberTheorem.logIntegral x :=
  PrimeNumberTheorem.logIntegral_pos hx

/-- Public asymptotic normalization `Li(x) ~ x/log x`. -/
theorem logIntegral_asymptotic :
    Tendsto
      (fun x : ℝ =>
        PrimeNumberTheorem.logIntegral x * Real.log x / x)
      atTop (𝓝 1) :=
  PrimeNumberTheorem.logIntegral_asymptotic

/-- Public little-o form of `Li(x)=o(x)`. -/
theorem logIntegral_isLittleO_id :
    (fun x : ℝ => PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.logIntegral_isLittleO_id

/-- Public entry point for the equivalence of the three PNT formulations used
in the project. -/
theorem pnt_forms_equiv :
    (PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm2) ∧
      (PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm3) :=
  PrimeNumberTheorem.pnt_forms_equivalent

/-- Public equivalence between the prime-counting and logarithmic-integral PNT
forms. -/
theorem pnt_form1_iff_pnt_form2 :
    PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm1_iff_PNTForm2

/-- Public equivalence between the logarithmic-integral and Chebyshev-ψ PNT
forms. -/
theorem pnt_form2_iff_pnt_form3 :
    PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm2_iff_PNTForm3

/-- Public transitive equivalence between the prime-counting and Chebyshev-ψ
PNT forms. -/
theorem pnt_form1_iff_pnt_form3 :
    PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm1_iff_PNTForm3

/-- Public equivalence between the Chebyshev-ψ PNT form and the Mathlib
Chebyshev-θ asymptotic. -/
theorem pnt_form3_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm3_iff_chebyshevTheta_asymptotic

/-- Public equivalence between the prime-counting PNT form and the Mathlib
Chebyshev-θ asymptotic. -/
theorem pnt_form1_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm1_iff_chebyshevTheta_asymptotic

/-- Public equivalence between the logarithmic-integral PNT form and the
Mathlib Chebyshev-θ asymptotic. -/
theorem pnt_form2_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm2_iff_chebyshevTheta_asymptotic

/-- Public equivalence between the Chebyshev-ψ PNT form and Mathlib's
Chebyshev-ψ asymptotic. -/
theorem pnt_form3_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm3_iff_mathlibChebyshevPsi_asymptotic

/-- Public equivalence between the prime-counting PNT form and Mathlib's
Chebyshev-ψ asymptotic. -/
theorem pnt_form1_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm1_iff_mathlibChebyshevPsi_asymptotic

/-- Public equivalence between the logarithmic-integral PNT form and Mathlib's
Chebyshev-ψ asymptotic. -/
theorem pnt_form2_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm2_iff_mathlibChebyshevPsi_asymptotic

/-- Public error-term form of `PNTForm1`. -/
theorem pnt_form1_iff_error_isLittleO_main :
    PrimeNumberTheorem.PNTForm1 ↔
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_iff_error_isLittleO_main

/-- Public error-term form of `PNTForm2`. -/
theorem pnt_form2_iff_error_isLittleO_logIntegral :
    PrimeNumberTheorem.PNTForm2 ↔
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x)
        =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_iff_error_isLittleO_logIntegral

/-- Public error-term form of `PNTForm3`. -/
theorem pnt_form3_iff_error_isLittleO_id :
    PrimeNumberTheorem.PNTForm3 ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
        =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_iff_error_isLittleO_id

/-! ### Exact-name PNT aliases

These aliases intentionally keep the theorem identifiers from
`PrimeNumberTheorem.lean` available through the public API namespace. -/

theorem pnt_forms_equivalent :
    (PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm2) ∧
      (PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm3) :=
  PrimeNumberTheorem.pnt_forms_equivalent

theorem PNTForm1_iff_PNTForm2 :
    PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm1_iff_PNTForm2

theorem PNTForm2_iff_PNTForm1 :
    PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm2_iff_PNTForm1

theorem PNTForm2_iff_PNTForm3 :
    PrimeNumberTheorem.PNTForm2 ↔ PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm2_iff_PNTForm3

theorem PNTForm3_iff_PNTForm2 :
    PrimeNumberTheorem.PNTForm3 ↔ PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm3_iff_PNTForm2

theorem PNTForm1_iff_PNTForm3 :
    PrimeNumberTheorem.PNTForm1 ↔ PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm1_iff_PNTForm3

theorem PNTForm3_iff_PNTForm1 :
    PrimeNumberTheorem.PNTForm3 ↔ PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm3_iff_PNTForm1

theorem PNTForm2_of_PNTForm1
    (h : PrimeNumberTheorem.PNTForm1) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_PNTForm1 h

theorem PNTForm1_of_PNTForm2
    (h : PrimeNumberTheorem.PNTForm2) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_PNTForm2 h

theorem PNTForm3_of_PNTForm2
    (h : PrimeNumberTheorem.PNTForm2) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_PNTForm2 h

theorem PNTForm2_of_PNTForm3
    (h : PrimeNumberTheorem.PNTForm3) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_PNTForm3 h

theorem PNTForm3_of_PNTForm1
    (h : PrimeNumberTheorem.PNTForm1) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_PNTForm1 h

theorem PNTForm1_of_PNTForm3
    (h : PrimeNumberTheorem.PNTForm3) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_PNTForm3 h

theorem PNTForm1_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm1_iff_chebyshevTheta_asymptotic

theorem PNTForm2_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm2_iff_chebyshevTheta_asymptotic

theorem PNTForm3_iff_chebyshevTheta_asymptotic :
    PrimeNumberTheorem.PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm3_iff_chebyshevTheta_asymptotic

theorem PNTForm1_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm1 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm1_iff_mathlibChebyshevPsi_asymptotic

theorem PNTForm2_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm2 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm2_iff_mathlibChebyshevPsi_asymptotic

theorem PNTForm3_iff_mathlibChebyshevPsi_asymptotic :
    PrimeNumberTheorem.PNTForm3 ↔
      Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.PNTForm3_iff_mathlibChebyshevPsi_asymptotic

theorem PNTForm1_error_isLittleO_main
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_error_isLittleO_main h

theorem PNTForm1_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm1_error_isLittleO_id h

theorem PNTForm1_error_isBigO_main
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_error_isBigO_main h

theorem PNTForm1_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm1_error_isBigO_id h

theorem PNTForm1_of_error_isLittleO_main
    (h :
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x)) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_error_isLittleO_main h

theorem PNTForm1_iff_error_isLittleO_main :
    PrimeNumberTheorem.PNTForm1 ↔
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_iff_error_isLittleO_main

theorem PNTForm2_error_isLittleO_logIntegral
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_error_isLittleO_logIntegral h

theorem PNTForm2_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm2_error_isLittleO_id h

theorem PNTForm2_error_isBigO_logIntegral
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_error_isBigO_logIntegral h

theorem PNTForm2_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm2_error_isBigO_id h

theorem PNTForm2_of_error_isLittleO_logIntegral
    (h :
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x)
        =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x)) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_error_isLittleO_logIntegral h

theorem PNTForm2_iff_error_isLittleO_logIntegral :
    PrimeNumberTheorem.PNTForm2 ↔
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x)
        =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_iff_error_isLittleO_logIntegral

theorem PNTForm3_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm3) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_error_isLittleO_id h

theorem PNTForm3_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm3) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_error_isBigO_id h

theorem PNTForm3_of_error_isLittleO_id
    (h :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
        =o[atTop] (fun x : ℝ => x)) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_error_isLittleO_id h

theorem PNTForm3_iff_error_isLittleO_id :
    PrimeNumberTheorem.PNTForm3 ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
        =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_iff_error_isLittleO_id

/-- Public Big-O bound for the logarithmic integral normalization. -/
theorem logIntegral_isBigO_id :
    (fun x : ℝ => PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.logIntegral_isBigO_id

/-- Public little-o estimate for the main PNT comparison denominator
`x/log x`. -/
theorem id_div_log_isLittleO_id :
    (fun x : ℝ => x / Real.log x) =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.id_div_log_isLittleO_id

/-- Public crude Big-O bound for the local prime-counting normalization. -/
theorem primeCounting_isBigO_id :
    (fun x : ℝ => (PrimeNumberTheorem.primeCounting x : ℝ))
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.primeCounting_isBigO_id

/-- Public crude Big-O bound for the `π(x) - Li(x)` error. -/
theorem primeCounting_sub_logIntegral_isBigO_id :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.primeCounting_sub_logIntegral_isBigO_id

/-- Public finite-interval bound for the local prime-counting normalization. -/
theorem primeCounting_le_floor_add_one {x X : ℝ} (hxX : x ≤ X) :
    PrimeNumberTheorem.primeCounting x ≤ ⌊X⌋₊ + 1 :=
  PrimeNumberTheorem.primeCounting_le_floor_add_one hxX

/-- Public crude upper bound for the logarithmic integral on a bounded
interval. -/
theorem logIntegral_le_interval_bound {x X : ℝ} (hx2 : 2 ≤ x)
    (hxX : x ≤ X) :
    PrimeNumberTheorem.logIntegral x ≤ (X - 2) / Real.log 2 :=
  PrimeNumberTheorem.logIntegral_le_interval_bound hx2 hxX

/-- Public lower bound for the RH prime-counting error scale on `[2, ∞)`. -/
theorem sqrt_mul_log_lower_bound {x : ℝ} (hx2 : 2 ≤ x) :
    Real.sqrt 2 * Real.log 2 ≤ Real.sqrt x * Real.log x :=
  PrimeNumberTheorem.sqrt_mul_log_lower_bound hx2

/-- Public finite-initial-interval control used to turn eventual RH-scale
prime-counting `Li` bounds into pointwise bounds. -/
theorem primeCounting_logIntegral_finite_interval_bound :
    ∀ X ≥ 2, ∃ C > 0, ∀ x, 2 ≤ x → x ≤ X →
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * (Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.primeCounting_logIntegral_finite_interval_bound

/-- Public error-term consequence of PNT form 1. -/
theorem pnt_form1_error_isLittleO_main
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_error_isLittleO_main h

/-- Public identity-scale little-o consequence of PNT form 1. -/
theorem pnt_form1_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm1_error_isLittleO_id h

/-- Public Big-O consequence of PNT form 1 at its natural scale. -/
theorem pnt_form1_error_isBigO_main
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x / Real.log x) :=
  PrimeNumberTheorem.PNTForm1_error_isBigO_main h

/-- Public identity-scale Big-O consequence of PNT form 1. -/
theorem pnt_form1_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm1) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm1_error_isBigO_id h

/-- Public constructor for PNT form 1 from its error-term formulation. -/
theorem pnt_form1_of_error_isLittleO_main
    (h :
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) - x / Real.log x)
        =o[atTop] (fun x : ℝ => x / Real.log x)) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_error_isLittleO_main h

/-- Public error-term consequence of PNT form 2 relative to `Li`. -/
theorem pnt_form2_error_isLittleO_logIntegral
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_error_isLittleO_logIntegral h

/-- Public Big-O consequence of PNT form 2 at the `Li` scale. -/
theorem pnt_form2_error_isBigO_logIntegral
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.PNTForm2_error_isBigO_logIntegral h

/-- Public constructor for PNT form 2 from its `Li` error-term formulation. -/
theorem pnt_form2_of_error_isLittleO_logIntegral
    (h :
      (fun x : ℝ =>
        (PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x)
        =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x)) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_error_isLittleO_logIntegral h

/-- Public error-term consequence of PNT form 2 relative to the identity
function. -/
theorem pnt_form2_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm2_error_isLittleO_id h

/-- Public identity-scale Big-O consequence of PNT form 2. -/
theorem pnt_form2_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm2) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm2_error_isBigO_id h

/-- Public error-term consequence of PNT form 3. -/
theorem pnt_form3_error_isLittleO_id
    (h : PrimeNumberTheorem.PNTForm3) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_error_isLittleO_id h

/-- Public identity-scale Big-O consequence of PNT form 3. -/
theorem pnt_form3_error_isBigO_id
    (h : PrimeNumberTheorem.PNTForm3) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.PNTForm3_error_isBigO_id h

/-- Public constructor for PNT form 3 from its error-term formulation. -/
theorem pnt_form3_of_error_isLittleO_id
    (h :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
        =o[atTop] (fun x : ℝ => x)) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_error_isLittleO_id h

/-- Public bridge from the `Li` RH-scale prime-counting target to the
logarithmic-integral PNT form. -/
theorem pnt_form2_of_rh_primeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_PrimeCountingLiErrorBound h

/-- Public bridge from the `Li` RH-scale prime-counting target to
`π(x) ~ x / log x`. -/
theorem pnt_form1_of_rh_primeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_PrimeCountingLiErrorBound h

/-- Public bridge from the `Li` RH-scale prime-counting target to the
Chebyshev-ψ PNT form. -/
theorem pnt_form3_of_rh_primeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_PrimeCountingLiErrorBound h

/-- Public bridge from the `Li` RH-scale prime-counting target to all three PNT
forms. -/
theorem pnt_forms_of_rh_primeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_PrimeCountingLiErrorBound h

/-- Public bridge from the textbook pointwise RH-scale prime-counting target to
all three PNT forms. -/
theorem pnt_forms_of_rh_error_bound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_ErrorBound h

/-- Public bridge from the textbook pointwise RH-scale prime-counting target
to `π(x) ~ x / log x`. -/
theorem pnt_form1_of_rh_error_bound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_ErrorBound h

/-- Public bridge from the textbook pointwise RH-scale prime-counting target
to `π(x) ~ Li(x)`. -/
theorem pnt_form2_of_rh_error_bound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_ErrorBound h

/-- Public bridge from the textbook pointwise RH-scale prime-counting target
to the Chebyshev-ψ PNT form. -/
theorem pnt_form3_of_rh_error_bound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_ErrorBound h

/-- Public bridge from the `ψ` RH-scale target to all three PNT forms. -/
theorem pnt_forms_of_rh_psi_error_bound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_PsiErrorBound h

/-- Public bridge from the `ψ` RH-scale target to `π(x) ~ x / log x`. -/
theorem pnt_form1_of_rh_psi_error_bound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_PsiErrorBound h

/-- Public bridge from the `ψ` RH-scale target to `π(x) ~ Li(x)`. -/
theorem pnt_form2_of_rh_psi_error_bound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_PsiErrorBound h

/-- Public bridge from the `ψ` RH-scale target to the Chebyshev-ψ PNT form. -/
theorem pnt_form3_of_rh_psi_error_bound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_PsiErrorBound h

/-- Public bridge from the `θ` RH-scale target to all three PNT forms. -/
theorem pnt_forms_of_rh_theta_error_bound
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_ThetaErrorBound h

/-- Public bridge from the `θ` RH-scale target to `π(x) ~ x / log x`. -/
theorem pnt_form1_of_rh_theta_error_bound
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_ThetaErrorBound h

/-- Public bridge from the `θ` RH-scale target to `π(x) ~ Li(x)`. -/
theorem pnt_form2_of_rh_theta_error_bound
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_ThetaErrorBound h

/-- Public bridge from the `θ` RH-scale target to the Chebyshev-ψ PNT form. -/
theorem pnt_form3_of_rh_theta_error_bound
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_ThetaErrorBound h

/-- Public entry point for the equivalence between the pointwise and
composable RH-scale prime-counting error targets. -/
theorem rh_error_bound_iff_composable :
    PrimeNumberTheorem.RH_ErrorBound ↔
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound

/-- Public bridge from the textbook pointwise RH-scale prime-counting target
to the composable Big-O target. -/
theorem rh_primeCountingLiErrorBound_of_rh_error_bound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ErrorBound h

/-- Public bridge from the composable Big-O RH-scale prime-counting target to
the textbook pointwise target. -/
theorem rh_error_bound_of_rh_primeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound h

/-- Public reverse orientation of the pointwise/composable RH-scale
prime-counting error equivalence. -/
theorem rh_primeCountingLiErrorBound_iff_rh_error_bound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound ↔
      PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound

/-- Public eventual-bound constructor for the `ψ` RH-scale Big-O target. -/
theorem rh_psi_error_bound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |PrimeNumberTheorem.chebyshevPsi x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_eventual_abs_bound h

/-- Public pointwise-bound constructor for the `ψ` RH-scale Big-O target. -/
theorem rh_psi_error_bound_of_pointwise {C : ℝ}
    (hC : 0 < C)
    (h : ∀ x ≥ 2,
      |PrimeNumberTheorem.chebyshevPsi x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_pointwise hC h

/-- Public eventual-bound constructor for the `θ` RH-scale Big-O target. -/
theorem rh_theta_error_bound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |Chebyshev.theta x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_eventual_abs_bound h

/-- Public pointwise-bound constructor for the `θ` RH-scale Big-O target. -/
theorem rh_theta_error_bound_of_pointwise {C : ℝ}
    (hC : 0 < C)
    (h : ∀ x ≥ 2,
      |Chebyshev.theta x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_pointwise hC h

/-- Public eventual-bound constructor for the prime-counting `Li` RH-scale
Big-O target. -/
theorem rh_primeCountingLiErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * (Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_eventual_abs_bound h

/-- Public conditional reverse bridge from the composable prime-counting
`Li` Big-O target to the textbook pointwise RH error target. -/
theorem rh_error_bound_of_rh_primeCountingLiErrorBound_of_finite_intervals
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (hfinite : ∀ X ≥ 2, ∃ C > 0, ∀ x, 2 ≤ x → x ≤ X →
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * (Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals
    h hfinite

/-- Public pointwise-bound constructor from the textbook RH error target to
the prime-counting `Li` Big-O target. -/
theorem rh_primeCountingLiErrorBound_of_pointwise
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_pointwise h

/-- Public little-o consequence of the prime-counting `Li` RH-scale Big-O
target. -/
theorem rh_primeCountingLiErrorBound_isLittleO_id
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound.isLittleO_id h

/-- Public little-o consequence of the textbook pointwise RH-scale
prime-counting target relative to `Li`. -/
theorem rh_error_bound_isLittleO_logIntegral
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.RH_ErrorBound.isLittleO_logIntegral h

/-- Public little-o consequence of the textbook pointwise RH-scale
prime-counting target relative to the identity function. -/
theorem rh_error_bound_isLittleO_id
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    (fun x : ℝ =>
      (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.RH_ErrorBound.isLittleO_id h

/-- Public little-o consequence of the `ψ` RH-scale Big-O target. -/
theorem rh_psi_error_bound_isLittleO_id
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.RH_PsiErrorBound.isLittleO_id h

/-- Public little-o consequence of the `θ` RH-scale Big-O target. -/
theorem rh_theta_error_bound_isLittleO_id
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    (fun x : ℝ => Chebyshev.theta x - x)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.RH_ThetaErrorBound.isLittleO_id h

/-- Public equivalence between the RH-scale ψ and θ error targets. -/
theorem rh_psi_error_bound_iff_rh_theta_error_bound :
    PrimeNumberTheorem.RH_PsiErrorBound ↔ PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_RH_ThetaErrorBound

/-- Public reverse orientation of the RH-scale ψ/θ error equivalence. -/
theorem rh_theta_error_bound_iff_rh_psi_error_bound :
    PrimeNumberTheorem.RH_ThetaErrorBound ↔ PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_iff_RH_PsiErrorBound

/-- Public implication from RH-scale ψ error to RH-scale θ error. -/
theorem rh_theta_error_bound_of_rh_psi_error_bound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_RH_PsiErrorBound hψ

/-- Public implication from RH-scale θ error to RH-scale ψ error. -/
theorem rh_psi_error_bound_of_rh_theta_error_bound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_RH_ThetaErrorBound hθ

/-- Public RH-scale bound for the gap between `ψ` and `θ`. -/
theorem psi_sub_theta_isBigO_rh_scale :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - Chebyshev.theta x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.psi_sub_theta_isBigO_rh_scale

/-- Public crude Big-O bound for Mathlib's Chebyshev `θ`. -/
theorem chebyshevTheta_isBigO_id :
    (fun x : ℝ => Chebyshev.theta x) =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.chebyshevTheta_isBigO_id

/-- Public crude Big-O bound for Mathlib's Chebyshev `ψ`. -/
theorem mathlibChebyshevPsi_isBigO_id :
    (fun x : ℝ => Chebyshev.psi x) =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_isBigO_id

/-- Public normalization bridge between the project ψ RH-scale target and
Mathlib's `Chebyshev.psi` error form. -/
theorem rh_psi_error_bound_iff_mathlibChebyshevPsi_sub_id_isBigO :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO

/-- Public forward direction of the Mathlib ψ normalization bridge. -/
theorem mathlibChebyshevPsi_sub_id_isBigO_of_rh_psi_error_bound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    (fun x : ℝ => Chebyshev.psi x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_sub_id_isBigO_of_RH_PsiErrorBound h

/-- Public reverse direction of the Mathlib ψ normalization bridge. -/
theorem rh_psi_error_bound_of_mathlibChebyshevPsi_sub_id_isBigO
    (h :
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_mathlibChebyshevPsi_sub_id_isBigO h

/-- Public crude Big-O bound for the local Chebyshev `ψ` normalization. -/
theorem chebyshevPsi_isBigO_id :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.chebyshevPsi_isBigO_id

/-- Public crude Big-O bound for the local Chebyshev `ψ(x)-x` error. -/
theorem chebyshevPsi_sub_id_isBigO_id :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x - x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.chebyshevPsi_sub_id_isBigO_id

/-- Public crude Big-O bound for the Chebyshev `θ(x)-x` error. -/
theorem chebyshevTheta_sub_id_isBigO_id :
    (fun x : ℝ => Chebyshev.theta x - x)
      =O[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.chebyshevTheta_sub_id_isBigO_id

/-- Public limit `log(x)^2 / sqrt(x) → 0`. -/
theorem log_sq_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => (Real.log x)^2 / Real.sqrt x) atTop (𝓝 0) :=
  PrimeNumberTheorem.log_sq_div_sqrt_tendsto_zero

/-- Public fact that the RH `ψ` scale is little-o of the identity. -/
theorem sqrt_mul_log_sq_isLittleO_id :
    (fun x : ℝ => Real.sqrt x * (Real.log x)^2)
      =o[atTop] (fun x : ℝ => x) :=
  PrimeNumberTheorem.sqrt_mul_log_sq_isLittleO_id

/-- Public fact that the project Chebyshev `ψ` and Mathlib Chebyshev `θ`
normalizations differ by `o(1)` after division by `x`. -/
theorem chebyshevPsi_sub_theta_div_id_tendsto_zero :
    Tendsto (fun x : ℝ =>
      (PrimeNumberTheorem.chebyshevPsi x - Chebyshev.theta x) / x)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.chebyshevPsi_sub_theta_div_id_tendsto_zero

/-- Public fact that the RH prime-counting scale is little-o of `Li(x)`. -/
theorem sqrt_mul_log_isLittleO_logIntegral :
    (fun x : ℝ => Real.sqrt x * Real.log x)
      =o[atTop] (fun x : ℝ => PrimeNumberTheorem.logIntegral x) :=
  PrimeNumberTheorem.sqrt_mul_log_isLittleO_logIntegral

/-- Public endpoint estimate in the partial-summation bridge from `θ` errors
to prime-counting errors. -/
theorem theta_error_div_log_isBigO_sqrt_mul_log
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    (fun x : ℝ => (Chebyshev.theta x - x) / Real.log x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.theta_error_div_log_isBigO_sqrt_mul_log hθ

/-- Public fixed-endpoint constant estimate in the partial-summation bridge. -/
theorem two_div_log_two_isBigO_sqrt_mul_log :
    (fun _x : ℝ => 2 / Real.log 2)
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.two_div_log_two_isBigO_sqrt_mul_log

/-- Public elementary tail-integral estimate used in the Abel integral bound. -/
theorem integral_one_div_sqrt_le_two_sqrt {A x : ℝ}
    (hA : 0 < A) (hAx : A ≤ x) :
    ∫ t in A..x, 1 / Real.sqrt t ≤ 2 * Real.sqrt x :=
  PrimeNumberTheorem.integral_one_div_sqrt_le_two_sqrt hA hAx

/-- Public interval-integrability package for the Abel error kernel. -/
theorem intervalIntegrable_theta_error_div_id_log_sq_of_le
    {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable
      (fun t : ℝ => (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
      MeasureTheory.volume a b :=
  PrimeNumberTheorem.intervalIntegrable_theta_error_div_id_log_sq_of_le ha hab

/-- Public Abel-integral estimate in the partial-summation bridge from `θ`
errors to prime-counting errors. -/
theorem theta_error_integral_isBigO_sqrt_mul_log
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    (fun x : ℝ =>
      ∫ t in (2)..x,
        (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
      =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x) :=
  PrimeNumberTheorem.theta_error_integral_isBigO_sqrt_mul_log hθ

/-- Public closed partial-summation bridge from the `θ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_theta_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound hθ

/-- Public closed partial-summation bridge from the `ψ` RH-scale target to the
prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_psi_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound hψ

/-- Public exact partial-summation identity connecting prime-counting `Li`
error to the Chebyshev-θ endpoint and Abel-integral errors. -/
theorem primeCounting_sub_logIntegral_eq_theta_error_integral
    {x : ℝ} (hx : 2 ≤ x) :
    (PrimeNumberTheorem.primeCounting x : ℝ) -
        PrimeNumberTheorem.logIntegral x =
      (Chebyshev.theta x - x) / Real.log x +
        (∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2)) +
        2 / Real.log 2 :=
  PrimeNumberTheorem.primeCounting_sub_logIntegral_eq_theta_error_integral hx

/-- Public bridge from the `θ` RH-scale target to the pointwise textbook
prime-counting RH error target. -/
theorem rh_error_bound_of_theta_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_ThetaErrorBound hθ

/-- Public bridge from the `ψ` RH-scale target to the pointwise textbook
prime-counting RH error target. -/
theorem rh_error_bound_of_psi_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PsiErrorBound hψ

/-- Public bound showing that the jump term between `ψ` and the midpoint
convention `ψ₀` is negligible at the RH error scale. -/
theorem jumpVonMangoldt_isBigO_rh_scale :
    (fun x : ℝ => PrimeNumberTheorem.jumpVonMangoldt x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.jumpVonMangoldt_isBigO_rh_scale

/-- Public equivalence between the RH-scale error target for `ψ` and the
corresponding midpoint-convention `ψ₀` target. -/
theorem rh_psi_error_bound_iff_chebyshevPsi0_sub_id_isBigO :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO

/-- Public forward direction from the `ψ` RH-scale target to the midpoint `ψ₀`
error target. -/
theorem chebyshevPsi0_sub_id_isBigO_of_RH_PsiErrorBound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.chebyshevPsi0_sub_id_isBigO_of_RH_PsiErrorBound hψ

/-- Public reverse direction from the midpoint `ψ₀` error target to the `ψ`
RH-scale target. -/
theorem rh_psi_error_bound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public bridge from the midpoint `ψ₀` RH-scale target to the prime-counting
`Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    hψ0

/-- Public bridge from the midpoint `ψ₀` RH-scale target to the pointwise
textbook prime-counting RH error target. -/
theorem rh_error_bound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public bridge from the midpoint `ψ₀` RH-scale target to PNT form 1. -/
theorem pnt_form1_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public bridge from the midpoint `ψ₀` RH-scale target to PNT form 2. -/
theorem pnt_form2_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public bridge from the midpoint `ψ₀` RH-scale target to PNT form 3. -/
theorem pnt_form3_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public all-three-PNT bridge from the midpoint `ψ₀` RH-scale target. -/
theorem pnt_forms_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_chebyshevPsi0_sub_id_isBigO hψ0

/-- Public bridge from the Mathlib Chebyshev-`θ` asymptotic to all three PNT
forms. -/
theorem pnt_forms_of_chebyshevTheta_asymptotic
    (hθ : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_chebyshevTheta_asymptotic hθ

/-- Public bridge from the Mathlib Chebyshev-`ψ` asymptotic to all three PNT
forms. -/
theorem pnt_forms_of_mathlibChebyshevPsi_asymptotic
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_mathlibChebyshevPsi_asymptotic hψ

/-- Public direct local Chebyshev-ψ asymptotic consequence of the `ψ`
RH-scale error target. -/
theorem chebyshevPsi_asymptotic_of_rh_psi_error_bound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x / x)
      atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevPsi_asymptotic_of_RH_PsiErrorBound hψ

/-- Public direct local Chebyshev-ψ asymptotic consequence of the `θ`
RH-scale error target. -/
theorem chebyshevPsi_asymptotic_of_rh_theta_error_bound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x / x)
      atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevPsi_asymptotic_of_RH_ThetaErrorBound hθ

/-- Public Mathlib Chebyshev-ψ asymptotic consequence of the local `ψ`
RH-scale error target. -/
theorem mathlibChebyshevPsi_asymptotic_of_rh_psi_error_bound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_asymptotic_of_RH_PsiErrorBound hψ

/-- Public Mathlib Chebyshev-ψ asymptotic consequence of the local `θ`
RH-scale error target. -/
theorem mathlibChebyshevPsi_asymptotic_of_rh_theta_error_bound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_asymptotic_of_RH_ThetaErrorBound hθ

/-- Public Mathlib Chebyshev-θ asymptotic consequence of the local `θ`
RH-scale error target. -/
theorem chebyshevTheta_asymptotic_of_rh_theta_error_bound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevTheta_asymptotic_of_RH_ThetaErrorBound hθ

/-- Public Mathlib Chebyshev-θ asymptotic consequence of the local `ψ`
RH-scale error target. -/
theorem chebyshevTheta_asymptotic_of_rh_psi_error_bound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevTheta_asymptotic_of_RH_PsiErrorBound hψ

/-! ### Exact-name RH/PNT bridge aliases -/

theorem PNTForm1_of_RH_PrimeCountingLiErrorBound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_PrimeCountingLiErrorBound

theorem PNTForm2_of_RH_PrimeCountingLiErrorBound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_PrimeCountingLiErrorBound

theorem PNTForm3_of_RH_PrimeCountingLiErrorBound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_PrimeCountingLiErrorBound

theorem PNTForm1_of_RH_ErrorBound :
    PrimeNumberTheorem.RH_ErrorBound → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_ErrorBound

theorem PNTForm2_of_RH_ErrorBound :
    PrimeNumberTheorem.RH_ErrorBound → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_ErrorBound

theorem PNTForm3_of_RH_ErrorBound :
    PrimeNumberTheorem.RH_ErrorBound → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_ErrorBound

theorem PNTForm1_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_PsiErrorBound

theorem PNTForm2_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_PsiErrorBound

theorem PNTForm3_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_PsiErrorBound

theorem PNTForm1_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_RH_ThetaErrorBound

theorem PNTForm2_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_RH_ThetaErrorBound

theorem PNTForm3_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_RH_ThetaErrorBound

theorem PNTForm1_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem PNTForm2_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem PNTForm3_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem PNTForms_of_RH_PrimeCountingLiErrorBound
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_PrimeCountingLiErrorBound h

theorem PNTForms_of_RH_ErrorBound
    (h : PrimeNumberTheorem.RH_ErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_ErrorBound h

theorem PNTForms_of_RH_PsiErrorBound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_PsiErrorBound h

theorem PNTForms_of_RH_ThetaErrorBound
    (h : PrimeNumberTheorem.RH_ThetaErrorBound) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_RH_ThetaErrorBound h

theorem PNTForms_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem PNTForms_of_chebyshevTheta_asymptotic
    (hθ : Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_chebyshevTheta_asymptotic hθ

theorem PNTForms_of_mathlibChebyshevPsi_asymptotic
    (hψ : Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1)) :
    PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
      PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_mathlibChebyshevPsi_asymptotic hψ

theorem RH_PsiErrorBound_iff_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_RH_ThetaErrorBound

theorem RH_ThetaErrorBound_iff_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound ↔
      PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_iff_RH_PsiErrorBound

theorem RH_ThetaErrorBound_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound →
      PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_RH_PsiErrorBound

theorem RH_PsiErrorBound_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound →
      PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_RH_ThetaErrorBound

theorem RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_chebyshevPsi0_sub_id_isBigO

theorem RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO :
    PrimeNumberTheorem.RH_PsiErrorBound ↔
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.RH_PsiErrorBound_iff_mathlibChebyshevPsi_sub_id_isBigO

theorem mathlibChebyshevPsi_sub_id_isBigO_of_RH_PsiErrorBound
    (h : PrimeNumberTheorem.RH_PsiErrorBound) :
    (fun x : ℝ => Chebyshev.psi x - x)
      =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_sub_id_isBigO_of_RH_PsiErrorBound h

theorem RH_PsiErrorBound_of_mathlibChebyshevPsi_sub_id_isBigO
    (h :
      (fun x : ℝ => Chebyshev.psi x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_mathlibChebyshevPsi_sub_id_isBigO h

theorem RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound

theorem RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound

theorem RH_PrimeCountingLiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_chebyshevPsi0_sub_id_isBigO
    hψ0

theorem RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound :
    PrimeNumberTheorem.RH_ErrorBound ↔
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_iff_RH_PrimeCountingLiErrorBound

theorem RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound ↔
      PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RH_ErrorBound

theorem RH_PrimeCountingLiErrorBound_of_RH_ErrorBound :
    PrimeNumberTheorem.RH_ErrorBound →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ErrorBound

theorem RH_ErrorBound_of_RH_PrimeCountingLiErrorBound :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound

theorem RH_ErrorBound_of_RH_ThetaErrorBound :
    PrimeNumberTheorem.RH_ThetaErrorBound → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_ThetaErrorBound

theorem RH_ErrorBound_of_RH_PsiErrorBound :
    PrimeNumberTheorem.RH_PsiErrorBound → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PsiErrorBound

theorem RH_ErrorBound_of_chebyshevPsi0_sub_id_isBigO
    (hψ0 :
      (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi0 x - x)
        =O[atTop] (fun x : ℝ => Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_chebyshevPsi0_sub_id_isBigO hψ0

theorem RH_PsiErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |PrimeNumberTheorem.chebyshevPsi x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_eventual_abs_bound h

theorem RH_PsiErrorBound_of_pointwise {C : ℝ}
    (hC : 0 < C)
    (h : ∀ x ≥ 2,
      |PrimeNumberTheorem.chebyshevPsi x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_PsiErrorBound :=
  PrimeNumberTheorem.RH_PsiErrorBound_of_pointwise hC h

theorem RH_ThetaErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |Chebyshev.theta x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_eventual_abs_bound h

theorem RH_ThetaErrorBound_of_pointwise {C : ℝ}
    (hC : 0 < C)
    (h : ∀ x ≥ 2,
      |Chebyshev.theta x - x| ≤
        C * (Real.sqrt x * (Real.log x)^2)) :
    PrimeNumberTheorem.RH_ThetaErrorBound :=
  PrimeNumberTheorem.RH_ThetaErrorBound_of_pointwise hC h

theorem RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    hθ hintegral

theorem RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound_of_integral_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound_of_integral_error
    hψ hintegral

theorem RH_PrimeCountingLiErrorBound_of_eventual_abs_bound {C : ℝ}
    (h : ∀ᶠ x in atTop,
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * (Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_eventual_abs_bound h

theorem RH_PrimeCountingLiErrorBound_of_pointwise :
    PrimeNumberTheorem.RH_ErrorBound →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_pointwise

theorem RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals
    (h : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (hfinite : ∀ X ≥ 2, ∃ C > 0, ∀ x, 2 ≤ x → x ≤ X →
      |(PrimeNumberTheorem.primeCounting x : ℝ) -
          PrimeNumberTheorem.logIntegral x| ≤
        C * (Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_RH_PrimeCountingLiErrorBound_of_finite_intervals
    h hfinite

theorem chebyshevPsi_asymptotic_of_RH_PsiErrorBound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x / x)
      atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevPsi_asymptotic_of_RH_PsiErrorBound hψ

theorem chebyshevPsi_asymptotic_of_RH_ThetaErrorBound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => PrimeNumberTheorem.chebyshevPsi x / x)
      atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevPsi_asymptotic_of_RH_ThetaErrorBound hθ

theorem mathlibChebyshevPsi_asymptotic_of_RH_PsiErrorBound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_asymptotic_of_RH_PsiErrorBound hψ

theorem mathlibChebyshevPsi_asymptotic_of_RH_ThetaErrorBound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.psi x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.mathlibChebyshevPsi_asymptotic_of_RH_ThetaErrorBound hθ

theorem chebyshevTheta_asymptotic_of_RH_ThetaErrorBound
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevTheta_asymptotic_of_RH_ThetaErrorBound hθ

theorem chebyshevTheta_asymptotic_of_RH_PsiErrorBound
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound) :
    Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 1) :=
  PrimeNumberTheorem.chebyshevTheta_asymptotic_of_RH_PsiErrorBound hψ

theorem rh_iff_optimal_error_iff :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (RiemannHypothesis.Statement ↔
        PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff

theorem rh_iff_optimal_error_of_implications
    (h_forward :
      RiemannHypothesis.Statement →
        PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (h_reverse :
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
        RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_implications
    h_forward h_reverse

theorem rh_iff_optimal_error_of_pointwise_implications
    (h_forward : RiemannHypothesis.Statement → PrimeNumberTheorem.RH_ErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_ErrorBound → RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_pointwise_implications
    h_forward h_reverse

theorem RH_PrimeCountingLiErrorBound_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_rh_iff_optimal_error h

theorem RiemannHypothesis_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_optimal_error h

theorem RH_ErrorBound_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_rh_iff_optimal_error h

theorem PNTForm1_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_rh_iff_optimal_error h

theorem PNTForm2_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_rh_iff_optimal_error h

theorem PNTForm3_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_rh_iff_optimal_error h

theorem RiemannHypothesis_of_rh_iff_pointwise_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound → RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_pointwise_error h

theorem RH_PrimeCountingLiErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound ↔
      RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error h

theorem RH_ErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound ↔ RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RH_ErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error h

theorem PNTForms_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm1 ∧
      PrimeNumberTheorem.PNTForm2 ∧ PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_rh_iff_optimal_error h

theorem RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h

theorem RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h

theorem PNTForm1_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_mathlib_RH_of_rh_iff_optimal_error h

theorem PNTForm2_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_mathlib_RH_of_rh_iff_optimal_error h

theorem PNTForm3_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public conditional partial-summation bridge from the `θ` RH-scale target
to the prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_theta_error_and_integral_error
    (hθ : PrimeNumberTheorem.RH_ThetaErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_ThetaErrorBound_of_integral_error
    hθ hintegral

/-- Public conditional partial-summation bridge from the `ψ` RH-scale target
to the prime-counting `Li` RH-scale target. -/
theorem rh_primeCountingLiErrorBound_of_psi_error_and_integral_error
    (hψ : PrimeNumberTheorem.RH_PsiErrorBound)
    (hintegral :
      (fun x : ℝ =>
        ∫ t in (2)..x,
          (Chebyshev.theta t - t) / (t * Real.log t ^ 2))
        =O[atTop] (fun x : ℝ => Real.sqrt x * Real.log x)) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_RH_PsiErrorBound_of_integral_error
    hψ hintegral

/-- Public bridge between the project's RH/error target and Mathlib's RH
predicate. -/
theorem rh_iff_optimal_error_iff_mathlib :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔
        PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff_mathlib

/-- Public compatibility bridge between Mathlib's RH predicate and the local
`RiemannHypothesis.Statement` interface used in the project files. -/
theorem rh_statement_iff_mathlib :
    _root_.RiemannHypothesis ↔ _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.rh_statement_iff_mathlib

/-- Public pointwise textbook-error form of the project's RH/error target. -/
theorem rh_iff_pointwise_error_iff :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis.Statement ↔ PrimeNumberTheorem.RH_ErrorBound) :=
  PrimeNumberTheorem.rh_iff_pointwise_error_iff

/-- Public local-Statement form of the project's RH/error equivalence target. -/
theorem rh_iff_optimal_error_iff_statement :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis.Statement ↔
        PrimeNumberTheorem.RH_PrimeCountingLiErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff

/-- Public local-Statement packaging lemma for closing the RH/error target from
the two composable Big-O implications. -/
theorem rh_iff_optimal_error_of_statement_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_implications h_forward h_reverse

/-- Public local-Statement packaging lemma for closing the RH/error target from
the two pointwise textbook implications. -/
theorem rh_iff_optimal_error_of_statement_pointwise_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_ErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_ErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_pointwise_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from Mathlib-RH
implications in composable Big-O form. -/
theorem rh_iff_optimal_error_of_mathlib_implications
    (h_forward : _root_.RiemannHypothesis →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_mathlib_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from Mathlib-RH
implications in pointwise textbook form. -/
theorem rh_iff_optimal_error_of_mathlib_pointwise_implications
    (h_forward : _root_.RiemannHypothesis → PrimeNumberTheorem.RH_ErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_ErrorBound → _root_.RiemannHypothesis) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_mathlib_pointwise_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from a future RH-to-`ψ`
error theorem. -/
theorem rh_iff_optimal_error_of_RH_PsiErrorBound_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_PsiErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_RH_PsiErrorBound_implications
    h_forward h_reverse

/-- Public packaging lemma for closing the RH/error target from a future RH-to-`θ`
error theorem. -/
theorem rh_iff_optimal_error_of_RH_ThetaErrorBound_implications
    (h_forward : _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_ThetaErrorBound)
    (h_reverse : PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement) :
    PrimeNumberTheorem.rh_iff_optimal_error :=
  PrimeNumberTheorem.rh_iff_optimal_error_of_RH_ThetaErrorBound_implications
    h_forward h_reverse

/-- Public forward direction from the RH/error target plus Mathlib RH to the
composable prime-counting error bound. -/
theorem rh_primeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_mathlib_RH_of_rh_iff_optimal_error
    h

/-- Public forward direction from the RH/error target plus Mathlib RH to the
pointwise textbook prime-counting error bound. -/
theorem rh_error_bound_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public reverse direction from the composable prime-counting error bound to
Mathlib RH, assuming the RH/error target. -/
theorem mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound → _root_.RiemannHypothesis :=
  PrimeNumberTheorem.mathlib_RH_of_rh_iff_optimal_error h

/-- Public reverse direction from the pointwise textbook error bound to Mathlib
RH, assuming the RH/error target. -/
theorem mathlib_RH_of_rh_iff_pointwise_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound → _root_.RiemannHypothesis :=
  PrimeNumberTheorem.mathlib_RH_of_rh_iff_pointwise_error h

/-- Public local-Statement forward direction of the RH/error target. -/
theorem rh_primeCountingLiErrorBound_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.RH_PrimeCountingLiErrorBound :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_of_rh_iff_optimal_error h

/-- Public local-Statement reverse direction of the RH/error target. -/
theorem riemannHypothesis_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound →
      _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_optimal_error h

/-- Public local-Statement forward direction into the pointwise textbook RH
error target. -/
theorem rh_error_bound_of_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement → PrimeNumberTheorem.RH_ErrorBound :=
  PrimeNumberTheorem.RH_ErrorBound_of_rh_iff_optimal_error h

/-- Public local-Statement reverse direction from the pointwise textbook RH
error target. -/
theorem riemannHypothesis_statement_of_rh_iff_pointwise_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound →
      _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RiemannHypothesis_of_rh_iff_pointwise_error h

/-- Public reverse equivalence induced by the RH/error target in composable
Big-O form. -/
theorem rh_primeCountingLiErrorBound_iff_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_PrimeCountingLiErrorBound ↔
      _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RH_PrimeCountingLiErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    h

/-- Public reverse equivalence induced by the RH/error target in pointwise
textbook form. -/
theorem rh_error_bound_iff_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    PrimeNumberTheorem.RH_ErrorBound ↔
      _root_.RiemannHypothesis.Statement :=
  PrimeNumberTheorem.RH_ErrorBound_iff_RiemannHypothesis_of_rh_iff_optimal_error
    h

/-- Public local-Statement consequence: the RH/error target turns local RH into
all three PNT forms. -/
theorem pnt_forms_of_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement →
      PrimeNumberTheorem.PNTForm1 ∧ PrimeNumberTheorem.PNTForm2 ∧
        PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForms_of_rh_iff_optimal_error h

/-- Public Mathlib-facing pointwise textbook form of the RH/error equivalence
target. -/
theorem rh_iff_optimal_error_iff_mathlib_pointwise :
    PrimeNumberTheorem.rh_iff_optimal_error ↔
      (_root_.RiemannHypothesis ↔ PrimeNumberTheorem.RH_ErrorBound) :=
  PrimeNumberTheorem.rh_iff_optimal_error_iff_mathlib_pointwise

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 1. -/
theorem pnt_form1_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 2. -/
theorem pnt_form2_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public consequence: the RH/error target turns Mathlib RH into PNT form 3. -/
theorem pnt_form3_of_mathlib_RH_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_mathlib_RH_of_rh_iff_optimal_error h

/-- Public local-Statement consequence: the RH/error target turns local RH into
PNT form 1. -/
theorem pnt_form1_of_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm1 :=
  PrimeNumberTheorem.PNTForm1_of_rh_iff_optimal_error h

/-- Public local-Statement consequence: the RH/error target turns local RH into
PNT form 2. -/
theorem pnt_form2_of_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm2 :=
  PrimeNumberTheorem.PNTForm2_of_rh_iff_optimal_error h

/-- Public local-Statement consequence: the RH/error target turns local RH into
PNT form 3. -/
theorem pnt_form3_of_statement_of_rh_iff_optimal_error
    (h : PrimeNumberTheorem.rh_iff_optimal_error) :
    _root_.RiemannHypothesis.Statement → PrimeNumberTheorem.PNTForm3 :=
  PrimeNumberTheorem.PNTForm3_of_rh_iff_optimal_error h

/-- Public equivalence between Mathlib's RH predicate and the nontrivial-zero
line statement. -/
theorem rh_iff_nontrivial_zeros_on_line :
    _root_.RiemannHypothesis ↔
      ∀ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s → s.re = 1 / 2 :=
  PrimeNumberTheorem.rh_iff_nontrivial_zeros_on_line

/-- Public functional-equation symmetry for nontrivial zeros. -/
theorem nontrivial_zero_symmetric
    {ρ : ℂ} (hρ : riemannZeta ρ = 0)
    (hre : 0 < ρ.re) (hre' : ρ.re < 1) :
    riemannZeta (1 - ρ) = 0 :=
  PrimeNumberTheorem.nontrivial_zero_symmetric hρ hre hre'

/-- Public packaged symmetry: `1 - ρ` is a nontrivial zero whenever `ρ` is. -/
theorem nontrivial_zero_symmetric'
    {ρ : ℂ} (h : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    _root_.RiemannHypothesis.IsNontrivialZero (1 - ρ) :=
  PrimeNumberTheorem.nontrivial_zero_symmetric' h

/-- Public critical-strip location theorem for nontrivial zeta zeros. -/
theorem nontrivial_zero_in_critical_strip {s : ℂ}
    (hζ : riemannZeta s = 0)
    (hnt : ¬∃ n : ℕ, s = -2 * ((n : ℂ) + 1))
    (hs1 : s ≠ 1) :
    0 < s.re ∧ s.re < 1 :=
  PrimeNumberTheorem.nontrivial_zero_in_critical_strip hζ hnt hs1

/-- Public local isolated-zero statement for `riemannZeta` away from the pole. -/
theorem riemannZeta_not_frequently_zero_nhdsNE_of_ne_one
    {x : ℂ} (hx : x ≠ 1) :
    ¬ ∃ᶠ z in 𝓝[≠] x, riemannZeta z = 0 :=
  PrimeNumberTheorem.riemannZeta_not_frequently_zero_nhdsNE_of_ne_one hx

/-- Public local finiteness of nontrivial zeta zeros in bounded height. -/
theorem finite_nontrivial_zeros_bounded_height (T : ℝ) :
    Set.Finite
      {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧ |s.im| ≤ T} :=
  PrimeNumberTheorem.finite_nontrivial_zeros_bounded_height T

/-- Public real-height finite-set form for zeta zeros on the critical line. -/
theorem critical_line_zeta_zeros_bounded_height_finite (B : ℝ) :
    Set.Finite
      {t : ℝ | |t| ≤ B ∧
        riemannZeta ((0.5 : ℂ) + Complex.I * t) = 0} :=
  PrimeNumberTheorem.critical_line_zeta_zeros_bounded_height_finite B

/-- Public real-height finite-set form for Hardy `Z` zeros. -/
theorem hardyZ_zeros_bounded_height_finite (B : ℝ) :
    Set.Finite
      {t : ℝ | |t| ≤ B ∧ HardyTheorem.hardyZ t = 0} :=
  PrimeNumberTheorem.hardyZ_zeros_bounded_height_finite B

/-- Public simple-pole consequence at `s = 1`: `(s - 1)^2 ζ(s) → 0`. -/
theorem riemannZeta_pole_simple :
    Tendsto (fun s : ℂ => (s - 1) ^ 2 * riemannZeta s) (𝓝[≠] 1) (𝓝 0) :=
  PrimeNumberTheorem.riemannZeta_pole_simple

/-- Public RH symmetry consistency for nontrivial zeros. -/
theorem rh_zero_symmetric_self_consistent
    {ρ : ℂ}
    (hRH : _root_.RiemannHypothesis.Statement)
    (h : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ρ.re = 1 / 2 ∧ (1 - ρ).re = 1 / 2 :=
  PrimeNumberTheorem.rh_zero_symmetric_self_consistent hRH h

/-- Public membership criterion for the height-truncated nontrivial-zero
finset. -/
theorem mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ} :
    ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T ↔
      _root_.RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T :=
  PrimeNumberTheorem.mem_nontrivialZerosFinset

/-- Public emptiness criterion for the height-truncated nontrivial-zero finset. -/
theorem nontrivialZerosFinset_eq_empty_iff {T : ℝ} :
    PrimeNumberTheorem.nontrivialZerosFinset T = ∅ ↔
      ¬ ∃ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T :=
  PrimeNumberTheorem.nontrivialZerosFinset_eq_empty_iff

/-- Public nonemptiness criterion for the height-truncated nontrivial-zero
finset. -/
theorem nontrivialZerosFinset_nonempty_iff {T : ℝ} :
    (PrimeNumberTheorem.nontrivialZerosFinset T).Nonempty ↔
      ∃ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ T :=
  PrimeNumberTheorem.nontrivialZerosFinset_nonempty_iff

/-- Public constructor for membership in the height-truncated nontrivial-zero
finset. -/
theorem nontrivial_zero_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) (hT : |ρ.im| ≤ T) :
    ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T :=
  PrimeNumberTheorem.nontrivial_zero_mem_nontrivialZerosFinset hρ hT

/-- Public nonzero fact for nontrivial zeta zeros. -/
theorem nontrivial_zero_ne_zero {ρ : ℂ}
    (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) : ρ ≠ 0 :=
  PrimeNumberTheorem.nontrivial_zero_ne_zero hρ

/-- Public elementwise monotonicity of height-truncated nontrivial-zero
finsets. -/
theorem nontrivialZerosFinset_mono {T U : ℝ} (hTU : T ≤ U) {ρ : ℂ}
    (hρ : ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T) :
    ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset U :=
  PrimeNumberTheorem.nontrivialZerosFinset_mono hTU hρ

/-- Public monotonicity of the height-truncated nontrivial-zero finset. -/
theorem nontrivialZerosFinset_subset {T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.nontrivialZerosFinset T ⊆
      PrimeNumberTheorem.nontrivialZerosFinset U :=
  PrimeNumberTheorem.nontrivialZerosFinset_subset hTU

/-- Public empty-new-zeros criterion when the upper truncation height is no
larger than the old one. -/
theorem nontrivialZerosFinset_sdiff_eq_empty_of_le
    {T U : ℝ} (hUT : U ≤ T) :
    PrimeNumberTheorem.nontrivialZerosFinset U \
        PrimeNumberTheorem.nontrivialZerosFinset T = ∅ :=
  PrimeNumberTheorem.nontrivialZerosFinset_sdiff_eq_empty_of_le hUT

/-- Public exclusion criterion from a height-truncated nontrivial-zero finset. -/
theorem not_mem_nontrivialZerosFinset_of_height_lt {ρ : ℂ} {T : ℝ}
    (hT : T < |ρ.im|) :
    ρ ∉ PrimeNumberTheorem.nontrivialZerosFinset T :=
  PrimeNumberTheorem.not_mem_nontrivialZerosFinset_of_height_lt hT

/-- Public membership criterion for newly appearing zeros between two
truncation heights. -/
theorem mem_nontrivialZerosFinset_sdiff {ρ : ℂ} {T U : ℝ} :
    ρ ∈ (PrimeNumberTheorem.nontrivialZerosFinset U \
        PrimeNumberTheorem.nontrivialZerosFinset T) ↔
      _root_.RiemannHypothesis.IsNontrivialZero ρ ∧ |ρ.im| ≤ U ∧
        T < |ρ.im| :=
  PrimeNumberTheorem.mem_nontrivialZerosFinset_sdiff

/-- Public nonzero denominator fact for elements of the height-truncated
nontrivial-zero finset. -/
theorem ne_zero_of_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T) : ρ ≠ 0 :=
  PrimeNumberTheorem.ne_zero_of_mem_nontrivialZerosFinset hρ

/-- Public emptiness of the height-truncated nontrivial-zero finset at negative
height. -/
theorem nontrivialZerosFinset_eq_empty_of_neg {T : ℝ} (hT : T < 0) :
    PrimeNumberTheorem.nontrivialZerosFinset T = ∅ :=
  PrimeNumberTheorem.nontrivialZerosFinset_eq_empty_of_neg hT

/-- Public zero value of the finite nontrivial-zero sum at negative height. -/
theorem finiteNontrivialZeroSum_eq_zero_of_neg
    (x : ℝ) {T : ℝ} (hT : T < 0) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x T = 0 :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_eq_zero_of_neg x hT

/-- Public zero value of the finite nontrivial-zero sum when the truncation
finset is empty. -/
theorem finiteNontrivialZeroSum_eq_zero_of_nontrivialZerosFinset_eq_empty
    (x : ℝ) {T : ℝ}
    (hT : PrimeNumberTheorem.nontrivialZerosFinset T = ∅) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x T = 0 :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_eq_zero_of_nontrivialZerosFinset_eq_empty
    x hT

/-- Public forward symmetry of the height-truncated nontrivial-zero finset under
`ρ ↦ 1 - ρ`. -/
theorem one_sub_mem_nontrivialZerosFinset {ρ : ℂ} {T : ℝ}
    (hρ : ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T) :
    1 - ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T :=
  PrimeNumberTheorem.one_sub_mem_nontrivialZerosFinset hρ

/-- Public symmetry of the height-truncated nontrivial-zero finset under
`ρ ↦ 1 - ρ`. -/
theorem one_sub_mem_nontrivialZerosFinset_iff {ρ : ℂ} {T : ℝ} :
    1 - ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T ↔
      ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T :=
  PrimeNumberTheorem.one_sub_mem_nontrivialZerosFinset_iff

/-- Public symmetry identity for sums over the height-truncated nontrivial-zero
finset. -/
theorem sum_nontrivialZerosFinset_one_sub (T : ℝ) (f : ℂ → ℂ) :
    (∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, f (1 - ρ)) =
      ∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, f ρ :=
  PrimeNumberTheorem.sum_nontrivialZerosFinset_one_sub T f

/-- Public extensionality criterion for height-truncated nontrivial-zero
finsets. -/
theorem nontrivialZerosFinset_ext_of_height_iff {T U : ℝ}
    (h : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    PrimeNumberTheorem.nontrivialZerosFinset T =
      PrimeNumberTheorem.nontrivialZerosFinset U :=
  PrimeNumberTheorem.nontrivialZerosFinset_ext_of_height_iff h

/-- Public equality of height-truncated zero finsets under a global height
bound. -/
theorem nontrivialZerosFinset_eq_of_global_height_bound {B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B) :
    PrimeNumberTheorem.nontrivialZerosFinset T =
      PrimeNumberTheorem.nontrivialZerosFinset B :=
  PrimeNumberTheorem.nontrivialZerosFinset_eq_of_global_height_bound hBT hbound

/-- Public stability of the finite nontrivial-zero sum under a global height
bound. -/
theorem finiteNontrivialZeroSum_eq_of_global_height_bound {x B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x T =
      PrimeNumberTheorem.finiteNontrivialZeroSum x B :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_eq_of_global_height_bound hBT hbound

/-- Public congruence of finite zero sums from equality of truncation finsets. -/
theorem finiteNontrivialZeroSum_congr_finset {x T U : ℝ}
    (h : PrimeNumberTheorem.nontrivialZerosFinset T =
      PrimeNumberTheorem.nontrivialZerosFinset U) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x T =
      PrimeNumberTheorem.finiteNontrivialZeroSum x U :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_congr_finset h

/-- Public congruence of finite zero sums from equivalent height predicates. -/
theorem finiteNontrivialZeroSum_congr_height {x T U : ℝ}
    (h : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x T =
      PrimeNumberTheorem.finiteNontrivialZeroSum x U :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_congr_height h

/-- Public decomposition of a larger zero sum into an old sum plus newly included
zeros. -/
theorem finiteNontrivialZeroSum_eq_add_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x U =
      PrimeNumberTheorem.finiteNontrivialZeroSum x T +
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_eq_add_new_zeros hTU

/-- Public subtraction form of the new-zero contribution between truncation
heights. -/
theorem finiteNontrivialZeroSum_sub_eq_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x U -
        PrimeNumberTheorem.finiteNontrivialZeroSum x T =
      ∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_sub_eq_new_zeros hTU

/-- Public stability of finite zero sums when no new zeros enter between
truncation heights. -/
theorem finiteNontrivialZeroSum_eq_of_sdiff_eq_empty
    {x T U : ℝ} (hTU : T ≤ U)
    (hnew : PrimeNumberTheorem.nontrivialZerosFinset U \
        PrimeNumberTheorem.nontrivialZerosFinset T = ∅) :
    PrimeNumberTheorem.finiteNontrivialZeroSum x U =
      PrimeNumberTheorem.finiteNontrivialZeroSum x T :=
  PrimeNumberTheorem.finiteNontrivialZeroSum_eq_of_sdiff_eq_empty hTU hnew

/-- Public congruence of explicit-formula truncations from equality of zero
finsets. -/
theorem explicitFormulaApprox_congr_finset {x T U : ℝ}
    (h : PrimeNumberTheorem.nontrivialZerosFinset T =
      PrimeNumberTheorem.nontrivialZerosFinset U) :
    PrimeNumberTheorem.explicitFormulaApprox x T =
      PrimeNumberTheorem.explicitFormulaApprox x U :=
  PrimeNumberTheorem.explicitFormulaApprox_congr_finset h

/-- Public congruence of explicit-formula truncations from equality of zero
sums. -/
theorem explicitFormulaApprox_congr_zero_sum {x T U : ℝ}
    (h : PrimeNumberTheorem.finiteNontrivialZeroSum x T =
      PrimeNumberTheorem.finiteNontrivialZeroSum x U) :
    PrimeNumberTheorem.explicitFormulaApprox x T =
      PrimeNumberTheorem.explicitFormulaApprox x U :=
  PrimeNumberTheorem.explicitFormulaApprox_congr_zero_sum h

/-- Public congruence of explicit-formula truncations from equivalent height
predicates. -/
theorem explicitFormulaApprox_congr_height {x T U : ℝ}
    (h : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      (|ρ.im| ≤ T ↔ |ρ.im| ≤ U)) :
    PrimeNumberTheorem.explicitFormulaApprox x T =
      PrimeNumberTheorem.explicitFormulaApprox x U :=
  PrimeNumberTheorem.explicitFormulaApprox_congr_height h

/-- Public identity reducing the difference of explicit-formula truncations to
the difference of finite zero sums. -/
theorem explicitFormulaApprox_sub_explicitFormulaApprox (x T U : ℝ) :
    PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U =
      PrimeNumberTheorem.finiteNontrivialZeroSum x U -
        PrimeNumberTheorem.finiteNontrivialZeroSum x T :=
  PrimeNumberTheorem.explicitFormulaApprox_sub_explicitFormulaApprox x T U

/-- Public explicit expression for the larger truncation in terms of the older
truncation and newly included zeros. -/
theorem explicitFormulaApprox_eq_sub_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.explicitFormulaApprox x U =
      PrimeNumberTheorem.explicitFormulaApprox x T -
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ :=
  PrimeNumberTheorem.explicitFormulaApprox_eq_sub_new_zeros hTU

/-- Public expression for the change in the explicit-formula truncation as the
new zero contribution. -/
theorem explicitFormulaApprox_sub_eq_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.explicitFormulaApprox x T -
      PrimeNumberTheorem.explicitFormulaApprox x U =
      ∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ :=
  PrimeNumberTheorem.explicitFormulaApprox_sub_eq_new_zeros hTU

/-- Public norm identity for the change in explicit-formula truncations. -/
theorem explicitFormulaApprox_sub_norm_eq_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U‖ =
      ‖∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ :=
  PrimeNumberTheorem.explicitFormulaApprox_sub_norm_eq_new_zeros hTU

/-- Public add-back form of the new-zero contribution between truncation
heights. -/
theorem explicitFormulaApprox_add_new_zeros {x T U : ℝ} (hTU : T ≤ U) :
    PrimeNumberTheorem.explicitFormulaApprox x U +
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T),
          (x : ℂ) ^ ρ / ρ =
      PrimeNumberTheorem.explicitFormulaApprox x T :=
  PrimeNumberTheorem.explicitFormulaApprox_add_new_zeros hTU

/-- Public stability of explicit-formula truncations when no new zeros enter
between truncation heights. -/
theorem explicitFormulaApprox_eq_of_sdiff_eq_empty
    {x T U : ℝ} (hTU : T ≤ U)
    (hnew : PrimeNumberTheorem.nontrivialZerosFinset U \
        PrimeNumberTheorem.nontrivialZerosFinset T = ∅) :
    PrimeNumberTheorem.explicitFormulaApprox x U =
      PrimeNumberTheorem.explicitFormulaApprox x T :=
  PrimeNumberTheorem.explicitFormulaApprox_eq_of_sdiff_eq_empty hTU hnew

/-- Public stability of the explicit-formula truncation under a global height
bound for nontrivial zeros. -/
theorem explicitFormulaApprox_eq_of_global_height_bound {x B T : ℝ}
    (hBT : B ≤ T)
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B) :
    PrimeNumberTheorem.explicitFormulaApprox x T =
      PrimeNumberTheorem.explicitFormulaApprox x B :=
  PrimeNumberTheorem.explicitFormulaApprox_eq_of_global_height_bound hBT hbound

/-- Public eventual stability of the explicit-formula truncation under a global
height bound for nontrivial zeros. -/
theorem explicitFormulaApprox_eventually_eq_of_global_height_bound {x B : ℝ}
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B) :
    (fun T : ℝ => PrimeNumberTheorem.explicitFormulaApprox x T) =ᶠ[atTop]
      fun _T : ℝ => PrimeNumberTheorem.explicitFormulaApprox x B :=
  PrimeNumberTheorem.explicitFormulaApprox_eventually_eq_of_global_height_bound hbound

/-- Public explicit-formula truncation at negative height, where the finite
zero sum is empty. -/
theorem explicitFormulaApprox_eq_of_neg (x : ℝ) {T : ℝ} (hT : T < 0) :
    PrimeNumberTheorem.explicitFormulaApprox x T =
      (x : ℂ)
        - deriv riemannZeta 0 / riemannZeta 0
        - (1 / 2 : ℂ) * (Real.log (1 - x^(-2 : ℝ)) : ℂ) :=
  PrimeNumberTheorem.explicitFormulaApprox_eq_of_neg x hT

/-- Public closed-half-plane nonvanishing theorem for the Riemann zeta
function. -/
theorem zeta_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    riemannZeta s ≠ 0 :=
  ZetaValues.zeta_ne_zero_of_one_le_re hs

/-- Public coordinate form of zeta nonvanishing on `Re(s) ≥ 1`. -/
theorem zeta_ne_zero_re_im_of_one_le {β t : ℝ} (hβ : 1 ≤ β) :
    riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZetaValues.zeta_ne_zero_re_im_of_one_le hβ

/-- Public known-result form: zeta has no zeros on the line `Re(s)=1`. -/
theorem zeta_no_zeros_on_one_line :
    ∀ s : ℂ, s.re = 1 → riemannZeta s ≠ 0 :=
  KnownResults.zeta_no_zeros_on_one_line

/-- Public known-result form: zeta has no zeros on the line `Re(s)=0`. -/
theorem zeta_no_zeros_on_zero_line :
    ∀ s : ℂ, s.re = 0 → riemannZeta s ≠ 0 :=
  KnownResults.zeta_no_zeros_on_zero_line

/-- Public nonvanishing theorem for zeta in the closed left half-plane away
from the trivial zeros. -/
theorem riemannZeta_ne_zero_of_re_le_zero {s : ℂ} (hs : s.re ≤ 0)
    (htrivial : ∀ n : ℕ, s ≠ -2 * ((n : ℂ) + 1)) :
    riemannZeta s ≠ 0 :=
  PrimeNumberTheorem.riemannZeta_ne_zero_of_re_le_zero hs htrivial

/-- Public helper: a zeta zero on the critical line is a nontrivial zero and
belongs to the project's critical-line set. -/
theorem complex_critical_line_zero_is_nontrivial {s : ℂ}
    (hre : s.re = 1 / 2) (hzero : riemannZeta s = 0) :
    _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.complex_critical_line_zero_is_nontrivial hre hzero

/-- Public meromorphicity of ζ away from its pole. -/
theorem meromorphicAt_riemannZeta_of_ne_one (s : ℂ) (hs : s ≠ 1) :
    MeromorphicAt riemannZeta s :=
  ZeroFreeRegion.meromorphicAt_riemannZeta_of_ne_one s hs

/-- Public meromorphicity of ζ at its pole `s = 1`. -/
theorem meromorphicAt_riemannZeta_one :
    MeromorphicAt riemannZeta (1 : ℂ) :=
  ZeroFreeRegion.meromorphicAt_riemannZeta_one

/-- Public meromorphicity of ζ on closed balls. -/
theorem meromorphicOn_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn riemannZeta (Metric.closedBall c R) :=
  ZeroFreeRegion.meromorphicOn_riemannZeta_closedBall c R

/-- Public meromorphic order of ζ at its pole `s = 1`. -/
theorem meromorphicOrderAt_riemannZeta_one :
    meromorphicOrderAt riemannZeta (1 : ℂ) = (-1 : ℤ) :=
  ZeroFreeRegion.meromorphicOrderAt_riemannZeta_one

/-- Public divisor value of ζ at its pole on any meromorphic domain containing
`1`. -/
theorem divisor_riemannZeta_pole_one {U : Set ℂ}
    (hU : (1 : ℂ) ∈ U) (hζ : MeromorphicOn riemannZeta U) :
    MeromorphicOn.divisor riemannZeta U (1 : ℂ) = (-1 : ℤ) :=
  ZeroFreeRegion.divisor_riemannZeta_pole_one hU hζ

/-- Public local nonvanishing of the zeta pole unit at `1`. -/
theorem eventually_ne_zero_riemannZetaPoleUnitAtOne :
    ∀ᶠ s in 𝓝 (1 : ℂ), ZeroFreeRegion.riemannZetaPoleUnitAtOne s ≠ 0 :=
  ZeroFreeRegion.eventually_ne_zero_riemannZetaPoleUnitAtOne

/-- Public local nonvanishing of ζ in a punctured neighborhood of its pole
`1`. -/
theorem eventually_ne_zero_riemannZeta_nhdsNE_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ), riemannZeta s ≠ 0 :=
  ZeroFreeRegion.eventually_ne_zero_riemannZeta_nhdsNE_one

/-- Public reciprocal local model for ζ near its pole `1`. -/
theorem eventuallyEq_inv_riemannZeta_simpleZeroAtOne :
    (fun s : ℂ => (riemannZeta s)⁻¹)
      =ᶠ[𝓝[≠] (1 : ℂ)]
      ZeroFreeRegion.riemannZetaReciprocalModelAtOne :=
  ZeroFreeRegion.eventuallyEq_inv_riemannZeta_simpleZeroAtOne

/-- Public analyticity of the reciprocal zeta model at `1`. -/
theorem analyticAt_riemannZetaReciprocalModelAtOne :
    AnalyticAt ℂ ZeroFreeRegion.riemannZetaReciprocalModelAtOne (1 : ℂ) :=
  ZeroFreeRegion.analyticAt_riemannZetaReciprocalModelAtOne

/-- Public simple-zero derivative for the reciprocal zeta model at `1`. -/
theorem deriv_riemannZetaReciprocalModelAtOne_one :
    deriv ZeroFreeRegion.riemannZetaReciprocalModelAtOne (1 : ℂ) = 1 :=
  ZeroFreeRegion.deriv_riemannZetaReciprocalModelAtOne_one

/-- Public logarithmic-residue limit for the reciprocal of ζ at `1`. -/
theorem tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne :
    Tendsto
      (fun w : ℂ =>
        (w - 1) * logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) w)
      (𝓝[≠] (1 : ℂ)) (𝓝 1) :=
  ZeroFreeRegion.tendsto_mul_logDeriv_inv_riemannZeta_simpleZeroAtOne

/-- Public local relation between `logDeriv (1 / ζ)` and `-logDeriv ζ`. -/
theorem eventuallyEq_logDeriv_inv_riemannZeta :
    (fun s : ℂ => logDeriv (fun z : ℂ => (riemannZeta z)⁻¹) s)
      =ᶠ[𝓝[≠] (1 : ℂ)]
    (fun s : ℂ => -logDeriv riemannZeta s) :=
  ZeroFreeRegion.eventuallyEq_logDeriv_inv_riemannZeta

/-- Public logarithmic-residue limit for ζ at its simple pole `1`. -/
theorem tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne :
    Tendsto (fun w : ℂ => (w - 1) * logDeriv riemannZeta w)
      (𝓝[≠] (1 : ℂ)) (𝓝 (-1 : ℂ)) :=
  ZeroFreeRegion.tendsto_mul_logDeriv_riemannZeta_simplePoleAtOne

/-- Public local normalized bound for the zeta logarithmic derivative near
its pole. -/
theorem eventually_norm_mul_logDeriv_riemannZeta_le_two :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖(s - 1) * logDeriv riemannZeta s‖ ≤ 2 :=
  ZeroFreeRegion.eventually_norm_mul_logDeriv_riemannZeta_le_two

/-- Public flexible local normalized bound for the zeta logarithmic derivative:
any constant `C > 1` eventually bounds the normalized norm. -/
theorem eventually_norm_mul_logDeriv_riemannZeta_lt_const
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖(s - 1) * logDeriv riemannZeta s‖ < C :=
  ZeroFreeRegion.eventually_norm_mul_logDeriv_riemannZeta_lt_const C hC

/-- Public local pole-order norm bound for the zeta logarithmic derivative. -/
theorem eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one

/-- Public flexible local pole-order norm bound for the zeta logarithmic
derivative. -/
theorem eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖logDeriv riemannZeta s‖ < C / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_logDeriv_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public local pole-order norm bound near `1` in quotient notation `ζ'/ζ`. -/
theorem eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public flexible local pole-order norm bound near `1` in quotient notation
`ζ'/ζ`. -/
theorem eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public local pole-order norm bound near `1` for the signed quotient
`-ζ'/ζ`. -/
theorem eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public flexible local pole-order norm bound near `1` for `-ζ'/ζ`. -/
theorem eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      ‖-deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public local real-part pole-order norm bound near `1` for `-ζ'/ζ`. -/
theorem eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      |(-deriv riemannZeta s / riemannZeta s).re| ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public flexible local real-part bound near `1` for `-ζ'/ζ`. -/
theorem eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      |(-deriv riemannZeta s / riemannZeta s).re| < C / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public flexible local one-sided real-part bound near `1` for `-ζ'/ζ`. -/
theorem eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∀ᶠ s in 𝓝[≠] (1 : ℂ),
      (-deriv riemannZeta s / riemannZeta s).re < C / ‖s - 1‖ :=
  ZeroFreeRegion.eventually_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public punctured-ball form of the local pole-order norm bound for the
zeta logarithmic derivative. -/
theorem exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 < r →
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_ball_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one

/-- Public closed punctured-ball form of the local pole-order norm bound for
the zeta logarithmic derivative. -/
theorem exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖logDeriv riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_norm_logDeriv_riemannZeta_le_two_div_norm_sub_one

/-- Public closed punctured-ball pole-order bound in quotient notation
`ζ'/ζ`. -/
theorem exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public closed punctured-ball flexible pole-order norm bound in quotient
notation `ζ'/ζ`. -/
theorem exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_norm_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public closed punctured-ball pole-order bound for the signed quotient
`-ζ'/ζ`. -/
theorem exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖-deriv riemannZeta s / riemannZeta s‖ ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public closed punctured-ball flexible pole-order norm bound for
`-ζ'/ζ`. -/
theorem exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      ‖-deriv riemannZeta s / riemannZeta s‖ < C / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public closed punctured-ball real-part bound for `-ζ'/ζ`. -/
theorem exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      |(-deriv riemannZeta s / riemannZeta s).re| ≤ 2 / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_norm_sub_one

/-- Public closed punctured-ball real-part bound for `-ζ'/ζ`, with any
constant `C > 1`. -/
theorem exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      |(-deriv riemannZeta s / riemannZeta s).re| < C / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public closed punctured-ball one-sided real-part bound for `-ζ'/ζ`,
with any constant `C > 1`. -/
theorem exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ r > 0, ∀ s : ℂ, s ≠ 1 → dist s 1 ≤ r →
      (-deriv riemannZeta s / riemannZeta s).re < C / ‖s - 1‖ :=
  ZeroFreeRegion.exists_punctured_closedBall_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_norm_sub_one C hC

/-- Public real-axis specialization of the local norm bound with constant `2`
for `-ζ'/ζ` near the pole at `1`. -/
theorem exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ ≤ 2 / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one

/-- Public real-axis specialization of the local real-part bound with constant
`2` for `-ζ'/ζ` near the pole at `1`. -/
theorem exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      |(-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re| ≤ 2 / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one

/-- Public real-axis one-sided local real-part bound with constant `2` for
`-ζ'/ζ` near the pole at `1`. -/
theorem exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re ≤ 2 / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_le_two_div_sub_one

/-- Public package of the concrete real-axis local bound in the `hreal` shape
used by the 3-4-1 high-height assembly. -/
theorem exists_rightNeighborhood_hreal_two_div_sub_one (T0 : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ σOf : ℝ → ℝ,
      (∀ t : ℝ, T0 ≤ |t| → 1 < σOf t) →
      (∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 1 + d) →
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          2 / (σOf t - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_hreal_two_div_sub_one T0

/-- Public concrete real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`. -/
theorem exists_sigmaOf_log_hreal_two_div_sub_one (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          2 / ((1 + a / Real.log |t|) - 1) :=
  ZeroFreeRegion.exists_sigmaOf_log_hreal_two_div_sub_one T0 hT0

/-- Public concrete real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`, normalized as an `O(log |t|)` estimate. -/
theorem exists_sigmaOf_log_hreal_two_mul_log_div (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          2 * Real.log |t| / a :=
  ZeroFreeRegion.exists_sigmaOf_log_hreal_two_mul_log_div T0 hT0

/-- Public real-axis specialization of the local norm bound for `-ζ'/ζ`
near the pole at `1`. -/
theorem exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      ‖-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)‖ < C / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_norm_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one C hC

/-- Public real-axis specialization of the local real-part bound for
`-ζ'/ζ` near the pole at `1`. -/
theorem exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      |(-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re| < C / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_abs_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one C hC

/-- Public real-axis one-sided specialization of the local real-part bound for
`-ζ'/ζ` near the pole at `1`. -/
theorem exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one
    (C : ℝ) (hC : 1 < C) :
    ∃ d : ℝ, 0 < d ∧ ∀ σ : ℝ, 1 < σ → σ ≤ 1 + d →
      (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re < C / (σ - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_re_neg_deriv_riemannZeta_div_riemannZeta_lt_const_div_sub_one C hC

/-- Public flexible package of the real-axis local bound in the `hreal` shape
used by the 3-4-1 high-height assembly. -/
theorem exists_rightNeighborhood_hreal_const_div_sub_one (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ σOf : ℝ → ℝ,
      (∀ t : ℝ, T0 ≤ |t| → 1 < σOf t) →
      (∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 1 + d) →
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          C / (σOf t - 1) :=
  ZeroFreeRegion.exists_rightNeighborhood_hreal_const_div_sub_one C hC T0

/-- Public flexible real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`. -/
theorem exists_sigmaOf_log_hreal_const_div_sub_one (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          C / ((1 + a / Real.log |t|) - 1) :=
  ZeroFreeRegion.exists_sigmaOf_log_hreal_const_div_sub_one C hC T0 hT0

/-- Public flexible real-axis `hreal` bound for
`σOf t = 1 + a / log |t|`, normalized as an `O(log |t|)` estimate. -/
theorem exists_sigmaOf_log_hreal_const_mul_log_div (C : ℝ) (hC : 1 < C)
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ t : ℝ, T0 ≤ |t| →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) : ℂ)).re ≤
          C * Real.log |t| / a :=
  ZeroFreeRegion.exists_sigmaOf_log_hreal_const_mul_log_div C hC T0 hT0

/-- Public closure theorem for the standard choice
`σ(t) = 1 + a / log |t|` in the high-height 3-4-1 argument. -/
theorem exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0)
    {c : ℝ} (hc_pos : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ (zeroBound : ℝ → ℝ → ℝ) (twoBound : ℝ → ℝ),
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              zeroBound β t) →
        (∀ t : ℝ, T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              twoBound t) →
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          3 * (C * Real.log |t| / a) + 4 * zeroBound β t +
            twoBound t < 0) →
        ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_log_deriv_bounds
    C hC T0 hT0 hc_pos

/-- Public closure theorem for the standard `σ = 1 + a/log |t|` choice with
the usual shifted logarithmic-derivative bound shapes. -/
theorem exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds
    (C : ℝ) (hC : 1 < C) (T0 : ℝ) (hT0 : 2 ≤ T0)
    {c : ℝ} (hc_pos : 0 < c) :
    ∃ d : ℝ, 0 < d ∧ ∀ a : ℝ, 0 < a → a ≤ Real.log 2 →
      a ≤ d * Real.log 2 →
      ∀ Czero Ctwo : ℝ,
        (3 * C / a + 4 * Czero + Ctwo < 4 / (a + c)) →
        (∀ β t : ℝ, T0 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                Czero * Real.log |t|) →
        (∀ t : ℝ, T0 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
              Ctwo * Real.log |t|) →
        ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.exists_sigmaOf_log_classical_zero_free_region_of_shift_bounds
    C hC T0 hT0 hc_pos

/-- Public high-level conditional closure of the classical zero-free region
from the two zeta-specific shifted logarithmic-derivative estimates. -/
theorem classical_zero_free_region_of_sigma_log_shift_estimates
    (C Czero Ctwo T0 : ℝ) (hC : 1 < C) (hC_lt : C < 4 / 3)
    (hK : 0 ≤ 4 * Czero + Ctwo) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates
    C Czero Ctwo T0 hC hC_lt hK hT0 hzero htwo

/-- Public concrete `5/4` real-axis coefficient version of the shifted-estimate
closure. -/
theorem classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths
    (Czero Ctwo T0 : ℝ) (hK : 0 ≤ 4 * Czero + Ctwo) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              Czero * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            Ctwo * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_five_fourths
    Czero Ctwo T0 hK hT0 hzero htwo

/-- Public same-constant version of the shifted-estimate closure. -/
theorem classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    (B T0 : ℝ) (hB : 0 ≤ B) (hT0 : 2 ≤ T0)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              B * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → T0 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * I * t)).re ≤
            B * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const
    B T0 hB hT0 hzero htwo

/-- Public meromorphicity of the zeta logarithmic derivative at `1`. -/
theorem meromorphicAt_logDeriv_riemannZeta_one :
    MeromorphicAt (logDeriv riemannZeta) (1 : ℂ) :=
  ZeroFreeRegion.meromorphicAt_logDeriv_riemannZeta_one

/-- Public meromorphicity of the zeta logarithmic derivative on closed balls. -/
theorem meromorphicOn_logDeriv_riemannZeta_closedBall (c : ℂ) (R : ℝ) :
    MeromorphicOn (logDeriv riemannZeta) (Metric.closedBall c R) :=
  ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_closedBall c R

/-- Public meromorphicity of ζ on a project vertical region. -/
theorem meromorphicOn_riemannZeta_verticalRegion (a b H : ℝ) :
    MeromorphicOn riemannZeta (ZeroFreeRegion.verticalRegion a b H) :=
  ZeroFreeRegion.meromorphicOn_riemannZeta_verticalRegion a b H

/-- Public meromorphicity of the logarithmic derivative of ζ on a project
vertical region. -/
theorem meromorphicOn_logDeriv_riemannZeta_verticalRegion (a b H : ℝ) :
    MeromorphicOn (logDeriv riemannZeta)
      (ZeroFreeRegion.verticalRegion a b H) :=
  ZeroFreeRegion.meromorphicOn_logDeriv_riemannZeta_verticalRegion a b H

/-- Public trigonometric core of de la Vallée Poussin's 3-4-1 inequality. -/
theorem trig_identity_nonneg (θ : ℝ) :
    3 + 4 * Real.cos θ + Real.cos (2 * θ) ≥ 0 :=
  ZeroFreeRegion.trig_identity_nonneg θ

/-- Public positivity of the real zeta function on `(1, ∞)`. -/
theorem riemannZeta_pos_of_real_gt_one (s : ℝ) (hs : 1 < s) :
    0 < (riemannZeta (s : ℂ)).re :=
  ZeroFreeRegion.riemannZeta_pos_of_real_gt_one s hs

/-- Public Euler-product logarithmic form for real zeta values. -/
theorem log_riemannZeta_dirichlet_series (s : ℝ) (hs : 1 < s) :
    Real.log (riemannZeta (s : ℂ)).re =
      ∑' p : Nat.Primes,
        Real.log (1 / (1 - (p : ℝ) ^ (-s))) :=
  ZeroFreeRegion.log_riemannZeta_dirichlet_series s hs

/-- Public real-part Dirichlet-series representation for the logarithmic
derivative of zeta in `Re(s)>1`. -/
theorem log_deriv_zeta_re_series (s : ℂ) (hs : 1 < s.re) :
    (-deriv riemannZeta s / riemannZeta s).re =
      ∑' n : ℕ,
        Λ n * Real.cos (s.im * Real.log n) / (n : ℝ) ^ s.re :=
  ZeroFreeRegion.log_deriv_zeta_re_series s hs

/-- Public real-valued series formula for `ζ(σ)` when `σ>1`. -/
theorem riemannZeta_re_eq_tsum_real (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, 1 / (↑n + 1 : ℝ) ^ σ :=
  ZeroFreeRegion.riemannZeta_re_eq_tsum_real σ hσ

/-- Public summability of the real zeta series for `σ>1`. -/
theorem summable_one_div_rpow (σ : ℝ) (hσ : 1 < σ) :
    Summable (fun n : ℕ => 1 / (↑n + 1 : ℝ) ^ σ) :=
  ZeroFreeRegion.summable_one_div_rpow σ hσ

/-- Public lower bound `ζ(σ)>1` on the real half-line `σ>1`. -/
theorem riemannZeta_re_gt_one (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re > 1 :=
  ZeroFreeRegion.riemannZeta_re_gt_one σ hσ

/-- Public integral-comparison lower bound for real zeta values. -/
theorem riemannZeta_gt_one_div_sub (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re > 1 / (σ - 1) :=
  ZeroFreeRegion.riemannZeta_gt_one_div_sub σ hσ

/-- Public complementary upper bound for real zeta values near the pole. -/
theorem riemannZeta_re_le_sigma_div_sub (σ : ℝ) (hσ : 1 < σ) :
    (riemannZeta (σ : ℂ)).re ≤ σ / (σ - 1) :=
  ZeroFreeRegion.riemannZeta_re_le_sigma_div_sub σ hσ

/-- Public residue sandwich at `s=1`: `1 < (σ-1)ζ(σ) ≤ σ`. -/
theorem residue_bounds (σ : ℝ) (hσ : 1 < σ) :
    1 < (σ - 1) * (riemannZeta (σ : ℂ)).re ∧
      (σ - 1) * (riemannZeta (σ : ℂ)).re ≤ σ :=
  ZeroFreeRegion.residue_bounds σ hσ

/-- Public positivity of the real logarithmic derivative series. -/
theorem log_deriv_zeta_pos_real (σ : ℝ) (hσ : 1 < σ) :
    0 < (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re :=
  ZeroFreeRegion.log_deriv_zeta_pos_real σ hσ

/-- Public pure-real specialization of the logarithmic-derivative Dirichlet
series. -/
theorem log_deriv_zeta_real_eq_series (σ : ℝ) (hσ : 1 < σ) :
    (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re =
      ∑' n : ℕ, Λ n / (n : ℝ) ^ σ :=
  ZeroFreeRegion.log_deriv_zeta_real_eq_series σ hσ

/-- Public antitonicity of `-Re(ζ'/ζ)` on the real half-line `(1, ∞)`. -/
theorem log_deriv_zeta_antitone
    {σ₁ σ₂ : ℝ} (hσ₁ : 1 < σ₁) (hσ₂ : σ₁ ≤ σ₂) :
    (-deriv riemannZeta (σ₂ : ℂ) / riemannZeta (σ₂ : ℂ)).re ≤
      (-deriv riemannZeta (σ₁ : ℂ) / riemannZeta (σ₁ : ℂ)).re :=
  ZeroFreeRegion.log_deriv_zeta_antitone hσ₁ hσ₂

/-- Public de la Vallée Poussin 3-4-1 nonnegativity combination. -/
theorem log_deriv_zeta_nonneg_combination (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    3 * (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      + 4 * (-deriv riemannZeta ((σ : ℂ) + Complex.I * t) /
          riemannZeta ((σ : ℂ) + Complex.I * t)).re
      + (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≥ 0 :=
  ZeroFreeRegion.log_deriv_zeta_nonneg_combination σ hσ t

/-- Public algebraic lower-bound corollary of the 3-4-1 inequality. -/
theorem log_deriv_zeta_lower_bound (σ : ℝ) (hσ : 1 < σ) (t : ℝ) :
    (-deriv riemannZeta ((σ : ℂ) + Complex.I * t) /
        riemannZeta ((σ : ℂ) + Complex.I * t)).re ≥
      -(3 / 4 : ℝ) *
        (-deriv riemannZeta (σ : ℂ) / riemannZeta (σ : ℂ)).re
      - (1 / 4 : ℝ) *
        (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re :=
  ZeroFreeRegion.log_deriv_zeta_lower_bound σ hσ t

/-- Public bridge from Mathlib's `logDeriv ζ` notation to `ζ'/ζ`. -/
theorem logDeriv_riemannZeta_eq_deriv_div (s : ℂ) :
    logDeriv riemannZeta s = deriv riemannZeta s / riemannZeta s :=
  ZeroFreeRegion.logDeriv_riemannZeta_eq_deriv_div s

/-- Public bridge from `-logDeriv ζ` to `-ζ'/ζ`. -/
theorem neg_logDeriv_riemannZeta_eq_neg_deriv_div (s : ℂ) :
    -logDeriv riemannZeta s = -deriv riemannZeta s / riemannZeta s :=
  ZeroFreeRegion.neg_logDeriv_riemannZeta_eq_neg_deriv_div s

/-- Public reverse bridge from `-ζ'/ζ` to `-logDeriv ζ`. -/
theorem neg_deriv_div_riemannZeta_eq_neg_logDeriv (s : ℂ) :
    -deriv riemannZeta s / riemannZeta s = -logDeriv riemannZeta s :=
  ZeroFreeRegion.neg_deriv_div_riemannZeta_eq_neg_logDeriv s

/-- Public real-part bridge from `logDeriv ζ` to `ζ'/ζ`. -/
theorem logDeriv_riemannZeta_re_eq_deriv_div_re (s : ℂ) :
    (logDeriv riemannZeta s).re =
      (deriv riemannZeta s / riemannZeta s).re :=
  ZeroFreeRegion.logDeriv_riemannZeta_re_eq_deriv_div_re s

/-- Public real-part bridge from `-logDeriv ζ` to `-ζ'/ζ`. -/
theorem neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re (s : ℂ) :
    (-logDeriv riemannZeta s).re =
      (-deriv riemannZeta s / riemannZeta s).re :=
  ZeroFreeRegion.neg_logDeriv_riemannZeta_re_eq_neg_deriv_div_re s

/-- Public reverse real-part bridge from `-ζ'/ζ` to `-logDeriv ζ`. -/
theorem neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re (s : ℂ) :
    (-deriv riemannZeta s / riemannZeta s).re =
      (-logDeriv riemannZeta s).re :=
  ZeroFreeRegion.neg_deriv_div_riemannZeta_re_eq_neg_logDeriv_re s

/-- Public norm bridge from `logDeriv ζ` to `ζ'/ζ`. -/
theorem norm_logDeriv_riemannZeta_eq_norm_deriv_div (s : ℂ) :
    ‖logDeriv riemannZeta s‖ =
      ‖deriv riemannZeta s / riemannZeta s‖ :=
  ZeroFreeRegion.norm_logDeriv_riemannZeta_eq_norm_deriv_div s

/-- Public norm bridge from `-ζ'/ζ` to `logDeriv ζ`. -/
theorem norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv (s : ℂ) :
    ‖-deriv riemannZeta s / riemannZeta s‖ =
      ‖logDeriv riemannZeta s‖ :=
  ZeroFreeRegion.norm_neg_deriv_div_riemannZeta_eq_norm_logDeriv s

/-- Public positivity of `log |t|` above height `2`. -/
theorem log_abs_pos_of_two_le {t : ℝ} (ht : 2 ≤ |t|) :
    0 < Real.log |t| :=
  ZeroFreeRegion.log_abs_pos_of_two_le ht

/-- Public lower bound `1 < log |t|` above height `3`. -/
theorem log_abs_gt_one_of_three_le {t : ℝ} (ht : 3 ≤ |t|) :
    1 < Real.log |t| :=
  ZeroFreeRegion.log_abs_gt_one_of_three_le ht

/-- Public positivity of the log-log factor above height `3`. -/
theorem log_log_abs_pos_of_three_le {t : ℝ} (ht : 3 ≤ |t|) :
    0 < Real.log (Real.log |t|) :=
  ZeroFreeRegion.log_log_abs_pos_of_three_le ht

/-- Public vertical region used by local zero-free-region estimates. -/
abbrev verticalRegion (a b H : ℝ) : Set ℂ :=
  ZeroFreeRegion.verticalRegion a b H

/-- Public membership characterization for `verticalRegion`. -/
theorem mem_verticalRegion {z : ℂ} {a b H : ℝ} :
    z ∈ verticalRegion a b H ↔ z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  ZeroFreeRegion.mem_verticalRegion

/-- Public fact that a positive-height vertical region excludes the pole `1`. -/
theorem one_not_mem_verticalRegion_of_pos_height {a b H : ℝ}
    (hH : 0 < H) :
    (1 : ℂ) ∉ verticalRegion a b H :=
  ZeroFreeRegion.one_not_mem_verticalRegion_of_pos_height hH

/-- Public fact that points in a positive-height vertical region are not the
pole `1`. -/
theorem ne_one_of_mem_verticalRegion_of_pos_height {z : ℂ} {a b H : ℝ}
    (hz : z ∈ verticalRegion a b H) (hH : 0 < H) :
    z ≠ 1 :=
  ZeroFreeRegion.ne_one_of_mem_verticalRegion_of_pos_height hz hH

/-- Public differentiability of ζ on positive-height vertical regions. -/
theorem differentiableOn_riemannZeta_verticalRegion_of_pos_height
    {a b H : ℝ} (hH : 0 < H) :
    DifferentiableOn ℂ riemannZeta (verticalRegion a b H) :=
  ZeroFreeRegion.differentiableOn_riemannZeta_verticalRegion_of_pos_height hH

/-- Public real/imaginary coordinate decomposition for complex numbers. -/
theorem re_im_decomp (s : ℂ) : ((s.re : ℂ) + Complex.I * s.im) = s :=
  ZeroFreeRegion.re_im_decomp s

/-- Public bound of real-coordinate displacement by complex norm. -/
theorem abs_re_sub_le_norm_sub (z c : ℂ) :
    |z.re - c.re| ≤ ‖z - c‖ :=
  ZeroFreeRegion.abs_re_sub_le_norm_sub z c

/-- Public bound of imaginary-coordinate displacement by complex norm. -/
theorem abs_im_sub_le_norm_sub (z c : ℂ) :
    |z.im - c.im| ≤ ‖z - c‖ :=
  ZeroFreeRegion.abs_im_sub_le_norm_sub z c

/-- Public real-coordinate bounds for a point in a closed complex ball. -/
theorem closedBall_re_bounds {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.closedBall c R) :
    c.re - R ≤ z.re ∧ z.re ≤ c.re + R :=
  ZeroFreeRegion.closedBall_re_bounds hz

/-- Public real-coordinate bounds for a point in an open complex ball. -/
theorem ball_re_bounds {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.ball c R) :
    c.re - R ≤ z.re ∧ z.re ≤ c.re + R :=
  ZeroFreeRegion.ball_re_bounds hz

/-- Public imaginary-height lower bound for a point in a closed complex ball. -/
theorem closedBall_abs_im_lower {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.closedBall c R) :
    |c.im| - R ≤ |z.im| :=
  ZeroFreeRegion.closedBall_abs_im_lower hz

/-- Public imaginary-height lower bound for a point in an open complex ball. -/
theorem ball_abs_im_lower {z c : ℂ} {R : ℝ}
    (hz : z ∈ Metric.ball c R) :
    |c.im| - R ≤ |z.im| :=
  ZeroFreeRegion.ball_abs_im_lower hz

/-- Public closed-ball height transfer from a high center to all points in the
ball. -/
theorem closedBall_abs_im_ge_of_add_le {z c : ℂ} {R H : ℝ}
    (hz : z ∈ Metric.closedBall c R) (hH : H + R ≤ |c.im|) :
    H ≤ |z.im| :=
  ZeroFreeRegion.closedBall_abs_im_ge_of_add_le hz hH

/-- Public open-ball height transfer from a high center to all points in the
ball. -/
theorem ball_abs_im_ge_of_add_le {z c : ℂ} {R H : ℝ}
    (hz : z ∈ Metric.ball c R) (hH : H + R ≤ |c.im|) :
    H ≤ |z.im| :=
  ZeroFreeRegion.ball_abs_im_ge_of_add_le hz hH

/-- Public real-coordinate bounds in a closed ball centered at `σ + I*t`. -/
theorem closedBall_sigma_it_re_bounds {z : ℂ} {σ t R : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + Complex.I * t) R) :
    σ - R ≤ z.re ∧ z.re ≤ σ + R :=
  ZeroFreeRegion.closedBall_sigma_it_re_bounds hz

/-- Public real-coordinate bounds in an open ball centered at `σ + I*t`. -/
theorem ball_sigma_it_re_bounds {z : ℂ} {σ t R : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    σ - R ≤ z.re ∧ z.re ≤ σ + R :=
  ZeroFreeRegion.ball_sigma_it_re_bounds hz

/-- Public height transfer in a closed ball centered at `σ + I*t`. -/
theorem closedBall_sigma_it_abs_im_ge_of_add_le {z : ℂ} {σ t R H : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + Complex.I * t) R)
    (hH : H + R ≤ |t|) :
    H ≤ |z.im| :=
  ZeroFreeRegion.closedBall_sigma_it_abs_im_ge_of_add_le hz hH

/-- Public height transfer in an open ball centered at `σ + I*t`. -/
theorem ball_sigma_it_abs_im_ge_of_add_le {z : ℂ} {σ t R H : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R)
    (hH : H + R ≤ |t|) :
    H ≤ |z.im| :=
  ZeroFreeRegion.ball_sigma_it_abs_im_ge_of_add_le hz hH

/-- Public real-strip membership for a closed ball centered at `σ + I*t`. -/
theorem closedBall_sigma_it_re_mem_Icc {z : ℂ} {σ t R a b : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + Complex.I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) :
    z.re ∈ Set.Icc a b :=
  ZeroFreeRegion.closedBall_sigma_it_re_mem_Icc hz ha hb

/-- Public real-strip membership for an open ball centered at `σ + I*t`. -/
theorem ball_sigma_it_re_mem_Icc {z : ℂ} {σ t R a b : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) :
    z.re ∈ Set.Icc a b :=
  ZeroFreeRegion.ball_sigma_it_re_mem_Icc hz ha hb

/-- Public vertical-region membership for a closed ball centered at `σ + I*t`. -/
theorem closedBall_sigma_it_mem_verticalRegion {z : ℂ} {σ t R a b H : ℝ}
    (hz : z ∈ Metric.closedBall ((σ : ℂ) + Complex.I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  ZeroFreeRegion.closedBall_sigma_it_mem_verticalRegion hz ha hb hH

/-- Public vertical-region membership for an open ball centered at `σ + I*t`. -/
theorem ball_sigma_it_mem_verticalRegion {z : ℂ} {σ t R a b H : ℝ}
    (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    z.re ∈ Set.Icc a b ∧ H ≤ |z.im| :=
  ZeroFreeRegion.ball_sigma_it_mem_verticalRegion hz ha hb hH

/-- Public closed-disk inclusion into a vertical region around a `σ + I*t`
center. -/
theorem closedBall_sigma_it_subset_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Metric.closedBall ((σ : ℂ) + Complex.I * t) R ⊆
      verticalRegion a b H :=
  ZeroFreeRegion.closedBall_sigma_it_subset_verticalRegion ha hb hH

/-- Public open-disk inclusion into a vertical region around a `σ + I*t`
center. -/
theorem ball_sigma_it_subset_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Metric.ball ((σ : ℂ) + Complex.I * t) R ⊆
      verticalRegion a b H :=
  ZeroFreeRegion.ball_sigma_it_subset_verticalRegion ha hb hH

/-- Public translated closed-disk map into a vertical region around a `σ + I*t`
center. -/
theorem mapsTo_add_closedBall_zero_sigma_it_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Set.MapsTo (fun w : ℂ => ((σ : ℂ) + Complex.I * t) + w)
      (Metric.closedBall 0 R) (verticalRegion a b H) :=
  ZeroFreeRegion.mapsTo_add_closedBall_zero_sigma_it_verticalRegion ha hb hH

/-- Public translated open-disk map into a vertical region around a `σ + I*t`
center. -/
theorem mapsTo_add_ball_zero_sigma_it_verticalRegion {σ t R a b H : ℝ}
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    Set.MapsTo (fun w : ℂ => ((σ : ℂ) + Complex.I * t) + w)
      (Metric.ball 0 R) (verticalRegion a b H) :=
  ZeroFreeRegion.mapsTo_add_ball_zero_sigma_it_verticalRegion ha hb hH

/-- Public differentiability restriction from a vertical region to a local
open disk centered at `σ + I*t`. -/
theorem differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
    {f : ℂ → ℂ} {σ t R a b H : ℝ}
    (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    DifferentiableOn ℂ f (Metric.ball ((σ : ℂ) + Complex.I * t) R) :=
  ZeroFreeRegion.differentiableOn_ball_sigma_it_of_differentiableOn_verticalRegion
    hf ha hb hH

/-- Public meromorphicity restriction from a vertical region to a local closed
disk centered at `σ + I*t`. -/
theorem meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion
    {f : ℂ → ℂ} {σ t R a b H : ℝ}
    (hf : MeromorphicOn f (verticalRegion a b H))
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|) :
    MeromorphicOn f (Metric.closedBall ((σ : ℂ) + Complex.I * t) R) :=
  ZeroFreeRegion.meromorphicOn_closedBall_sigma_it_of_meromorphicOn_verticalRegion
    hf ha hb hH

/-- Public Borel-Carathéodory theorem in the vanishing-at-zero form, routed
through the zero-free-region namespace. -/
theorem borelCaratheodory_zero
    {f : ℂ → ℂ} {M R : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R)
    (hf₂ : f 0 = 0) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) :=
  ZeroFreeRegion.borelCaratheodory_zero hM hf hf₁ hR hz hf₂

/-- Public Borel-Carathéodory theorem routed through the zero-free-region
namespace. -/
theorem borelCaratheodory
    {f : ℂ → ℂ} {M R : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hf₁ : Set.MapsTo f (Metric.ball 0 R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball 0 R) :
    ‖f z‖ ≤
      2 * M * ‖z‖ / (R - ‖z‖) +
        ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) :=
  ZeroFreeRegion.borelCaratheodory hM hf hf₁ hR hz

/-- Public centered Borel-Carathéodory theorem in the vanishing-at-center form. -/
theorem borelCaratheodory_zero_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo f (Metric.ball c R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R)
    (hf₂ : f c = 0) :
    ‖f z‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) :=
  ZeroFreeRegion.borelCaratheodory_zero_centered hM hf hf₁ hR hz hf₂

/-- Public centered Borel-Carathéodory theorem. -/
theorem borelCaratheodory_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo f (Metric.ball c R) {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) :
    ‖f z‖ ≤
      2 * M * ‖z - c‖ / (R - ‖z - c‖) +
        ‖f c‖ * (R + ‖z - c‖) / (R - ‖z - c‖) :=
  ZeroFreeRegion.borelCaratheodory_centered hM hf hf₁ hR hz

/-- Public centered Borel-Carathéodory oscillation estimate. -/
theorem borelCaratheodory_sub_centered
    {f : ℂ → ℂ} {M R : ℝ} {c z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball c R))
    (hf₁ : Set.MapsTo (fun w => f w - f c) (Metric.ball c R)
      {w | w.re ≤ M})
    (hR : 0 < R) (hz : z ∈ Metric.ball c R) :
    ‖f z - f c‖ ≤ 2 * M * ‖z - c‖ / (R - ‖z - c‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_centered hM hf hf₁ hR hz

/-- Public Borel-Carathéodory on a `σ + I*t` disk with ambient
vertical-region hypotheses. -/
theorem borelCaratheodory_centered_verticalRegion
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo f (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖f z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) +
        ‖f ((σ : ℂ) + Complex.I * t)‖ *
          (R + ‖z - ((σ : ℂ) + Complex.I * t)‖) /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_centered_verticalRegion
    hM hf hf₁ ha hb hH hR hz

/-- Public oscillation form of Borel-Carathéodory on a `σ + I*t` disk with
ambient vertical-region hypotheses. -/
theorem borelCaratheodory_sub_centered_verticalRegion
    {f : ℂ → ℂ} {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hf : DifferentiableOn ℂ f (verticalRegion a b H))
    (hf₁ : Set.MapsTo
      (fun w => f w - f ((σ : ℂ) + Complex.I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖f z - f ((σ : ℂ) + Complex.I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
        (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_centered_verticalRegion
    hM hf hf₁ ha hb hH hR hz

/-- Public Borel-Carathéodory bound specialized to ζ on a `σ + I*t` disk with
ambient vertical-region hypotheses. -/
theorem borelCaratheodory_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo riemannZeta (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) +
        ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ *
          (R + ‖z - ((σ : ℂ) + Complex.I * t)‖) /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion
    hM hHpos hζ ha hb hH hR hz

/-- Public oscillation Borel-Carathéodory bound specialized to ζ on a
`σ + I*t` disk with ambient vertical-region hypotheses. -/
theorem borelCaratheodory_sub_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : Set.MapsTo
      (fun w => riemannZeta w - riemannZeta ((σ : ℂ) + Complex.I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
        (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion
    hM hHpos hζ ha hb hH hR hz

/-- Public conversion from a pointwise real-part estimate for ζ to the
`Set.MapsTo` Borel-Carathéodory input. -/
theorem mapsTo_riemannZeta_verticalRegion_of_re_le
    {a b H M : ℝ}
    (hζ : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (riemannZeta z).re ≤ M) :
    Set.MapsTo riemannZeta (verticalRegion a b H) {w | w.re ≤ M} :=
  ZeroFreeRegion.mapsTo_riemannZeta_verticalRegion_of_re_le hζ

/-- Public conversion from a pointwise centered ζ real-part estimate to the
`Set.MapsTo` Borel-Carathéodory input. -/
theorem mapsTo_sub_riemannZeta_verticalRegion_of_re_le
    {σ t a b H M : ℝ}
    (hζ : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (riemannZeta z - riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤ M) :
    Set.MapsTo
      (fun z => riemannZeta z - riemannZeta ((σ : ℂ) + Complex.I * t))
      (verticalRegion a b H) {w | w.re ≤ M} :=
  ZeroFreeRegion.mapsTo_sub_riemannZeta_verticalRegion_of_re_le hζ

/-- Public pointwise-estimate form of Borel-Carathéodory specialized to ζ on a
`σ + I*t` disk. -/
theorem borelCaratheodory_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H → (riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) +
        ‖riemannZeta ((σ : ℂ) + Complex.I * t)‖ *
          (R + ‖z - ((σ : ℂ) + Complex.I * t)‖) /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_riemannZeta_verticalRegion_of_re_le
    hM hHpos hζ ha hb hH hR hz

/-- Public pointwise-estimate form of the oscillation Borel-Carathéodory
wrapper specialized to ζ. -/
theorem borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M) (hHpos : 0 < H)
    (hζ : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (riemannZeta w - riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖riemannZeta z - riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
        (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_riemannZeta_verticalRegion_of_re_le
    hM hHpos hζ ha hb hH hR hz

/-- Public conditional Borel-Carathéodory bound for the logarithmic derivative
of ζ on a `σ + I*t` disk. -/
theorem borelCaratheodory_logDeriv_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : Set.MapsTo (logDeriv riemannZeta)
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ *
          (R + ‖z - ((σ : ℂ) + Complex.I * t)‖) /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion
    hM hlogdiff hlog ha hb hH hR hz

/-- Public conditional oscillation form of Borel-Carathéodory for the
logarithmic derivative of ζ on a `σ + I*t` disk. -/
theorem borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : Set.MapsTo
      (fun w =>
        logDeriv riemannZeta w -
          logDeriv riemannZeta ((σ : ℂ) + Complex.I * t))
      (verticalRegion a b H) {w | w.re ≤ M})
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
        (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion
    hM hlogdiff hlog ha hb hH hR hz

/-- Public conversion from a pointwise real-part estimate for `logDeriv ζ` to
the `Set.MapsTo` Borel-Carathéodory input. -/
theorem mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le
    {a b H M : ℝ}
    (hlog : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (logDeriv riemannZeta z).re ≤ M) :
    Set.MapsTo (logDeriv riemannZeta)
      (verticalRegion a b H) {w | w.re ≤ M} :=
  ZeroFreeRegion.mapsTo_logDeriv_riemannZeta_verticalRegion_of_re_le hlog

/-- Public conversion from a pointwise centered `logDeriv ζ` real-part
estimate to the `Set.MapsTo` Borel-Carathéodory input. -/
theorem mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    {σ t a b H M : ℝ}
    (hlog : ∀ z : ℂ, z ∈ verticalRegion a b H →
      (logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤ M) :
    Set.MapsTo
      (fun z =>
        logDeriv riemannZeta z -
          logDeriv riemannZeta ((σ : ℂ) + Complex.I * t))
      (verticalRegion a b H) {w | w.re ≤ M} :=
  ZeroFreeRegion.mapsTo_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    hlog

/-- Public pointwise-estimate form of the conditional Borel-Carathéodory bound
for the logarithmic derivative of ζ on a `σ + I*t` disk. -/
theorem borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖logDeriv riemannZeta z‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) +
        ‖logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ *
          (R + ‖z - ((σ : ℂ) + Complex.I * t)‖) /
          (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_logDeriv_riemannZeta_verticalRegion_of_re_le
    hM hlogdiff hlog ha hb hH hR hz

/-- Public pointwise-estimate form of the conditional oscillation
Borel-Carathéodory bound for the logarithmic derivative of ζ. -/
theorem borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    {M R σ t a b H : ℝ} {z : ℂ}
    (hM : 0 < M)
    (hlogdiff :
      DifferentiableOn ℂ (logDeriv riemannZeta) (verticalRegion a b H))
    (hlog : ∀ w : ℂ, w ∈ verticalRegion a b H →
      (logDeriv riemannZeta w -
        logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)).re ≤ M)
    (ha : a + R ≤ σ) (hb : σ + R ≤ b) (hH : H + R ≤ |t|)
    (hR : 0 < R) (hz : z ∈ Metric.ball ((σ : ℂ) + Complex.I * t) R) :
    ‖logDeriv riemannZeta z -
        logDeriv riemannZeta ((σ : ℂ) + Complex.I * t)‖ ≤
      2 * M * ‖z - ((σ : ℂ) + Complex.I * t)‖ /
        (R - ‖z - ((σ : ℂ) + Complex.I * t)‖) :=
  ZeroFreeRegion.borelCaratheodory_sub_logDeriv_riemannZeta_verticalRegion_of_re_le
    hM hlogdiff hlog ha hb hH hR hz

section JensenWrapper

open MeromorphicAt MeromorphicOn Metric Real

/-- Public Jensen formula routed through the zero-free-region namespace. -/
theorem jensen_circleAverage_log_norm
    {c : ℂ} {R : ℝ} {f : ℂ → ℂ}
    (hR : R ≠ 0) (hf : MeromorphicOn f (closedBall c |R|)) :
    circleAverage (Real.log ‖f ·‖) c R
      = ∑ᶠ u, divisor f (closedBall c |R|) u * Real.log (R * ‖c - u‖⁻¹)
        + divisor f (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt f c‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm hR hf

/-- Public Jensen formula on a `σ + I*t` disk with ambient vertical-region
meromorphicity. -/
theorem jensen_circleAverage_log_norm_verticalRegion
    {f : ℂ → ℂ} {R σ t a b H : ℝ}
    (hR : R ≠ 0) (hf : MeromorphicOn f (verticalRegion a b H))
    (ha : a + |R| ≤ σ) (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖f ·‖) ((σ : ℂ) + Complex.I * t) R
      = ∑ᶠ u,
          divisor f (closedBall ((σ : ℂ) + Complex.I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + Complex.I * t) - u‖⁻¹)
        + divisor f (closedBall ((σ : ℂ) + Complex.I * t) |R|)
            ((σ : ℂ) + Complex.I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt f
            ((σ : ℂ) + Complex.I * t)‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm_verticalRegion
    hR hf ha hb hH

/-- Public Jensen formula specialized to ζ on a closed ball. -/
theorem jensen_circleAverage_log_norm_riemannZeta_closedBall
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖riemannZeta ·‖) c R
      = ∑ᶠ u, divisor riemannZeta (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor riemannZeta (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta c‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_closedBall hR

/-- Public Jensen formula specialized to ζ on a `σ + I*t` disk using ambient
vertical-region bookkeeping. -/
theorem jensen_circleAverage_log_norm_riemannZeta_verticalRegion
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖riemannZeta ·‖)
        ((σ : ℂ) + Complex.I * t) R
      = ∑ᶠ u,
          divisor riemannZeta
            (closedBall ((σ : ℂ) + Complex.I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + Complex.I * t) - u‖⁻¹)
        + divisor riemannZeta
            (closedBall ((σ : ℂ) + Complex.I * t) |R|)
            ((σ : ℂ) + Complex.I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt riemannZeta
            ((σ : ℂ) + Complex.I * t)‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm_riemannZeta_verticalRegion
    hR ha hb hH

/-- Public Jensen formula specialized to the logarithmic derivative of ζ on a
closed ball. -/
theorem jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall
    {c : ℂ} {R : ℝ} (hR : R ≠ 0) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖) c R
      = ∑ᶠ u, divisor (logDeriv riemannZeta) (closedBall c |R|) u *
          Real.log (R * ‖c - u‖⁻¹)
        + divisor (logDeriv riemannZeta) (closedBall c |R|) c * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta) c‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_closedBall hR

/-- Public Jensen formula specialized to the logarithmic derivative of ζ on a
`σ + I*t` disk using ambient vertical-region bookkeeping. -/
theorem jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion
    {R σ t a b H : ℝ}
    (hR : R ≠ 0) (ha : a + |R| ≤ σ)
    (hb : σ + |R| ≤ b) (hH : H + |R| ≤ |t|) :
    circleAverage (Real.log ‖logDeriv riemannZeta ·‖)
        ((σ : ℂ) + Complex.I * t) R
      = ∑ᶠ u,
          divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + Complex.I * t) |R|) u *
            Real.log (R * ‖((σ : ℂ) + Complex.I * t) - u‖⁻¹)
        + divisor (logDeriv riemannZeta)
            (closedBall ((σ : ℂ) + Complex.I * t) |R|)
            ((σ : ℂ) + Complex.I * t) * Real.log R
        + Real.log ‖meromorphicTrailingCoeffAt (logDeriv riemannZeta)
            ((σ : ℂ) + Complex.I * t)‖ :=
  ZeroFreeRegion.jensen_circleAverage_log_norm_logDeriv_riemannZeta_verticalRegion
    hR ha hb hH

end JensenWrapper

/-- Public Phragmén-Lindelöf vertical-strip principle routed through the
zero-free-region namespace. -/
theorem phragmenLindelof_vertical_strip
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {a b C : ℝ} {z : ℂ}
    (hfd : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hB : ∃ c < Real.pi / (b - a), ∃ B,
      f =O[Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z => Real.exp (B * Real.exp (c * |z.im|)))
    (hle_a : ∀ z : ℂ, Complex.re z = a → ‖f z‖ ≤ C)
    (hle_b : ∀ z : ℂ, Complex.re z = b → ‖f z‖ ≤ C)
    (hza : a ≤ Complex.re z) (hzb : Complex.re z ≤ b) :
    ‖f z‖ ≤ C :=
  ZeroFreeRegion.phragmenLindelof_vertical_strip
    hfd hB hle_a hle_b hza hzb

/-- Public Hadamard three-lines theorem routed through the zero-free-region
namespace. -/
theorem hadamardThreeLines_norm_le_interp
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {f : ℂ → E} {z : ℂ} {A B l u : ℝ}
    (hul : l < u)
    (hz : z ∈ Complex.HadamardThreeLines.verticalClosedStrip l u)
    (hd : DiffContOnCl ℂ f (Complex.HadamardThreeLines.verticalStrip l u))
    (hB : BddAbove
      ((norm ∘ f) '' Complex.HadamardThreeLines.verticalClosedStrip l u))
    (ha : ∀ z ∈ Complex.re ⁻¹' {l}, ‖f z‖ ≤ A)
    (hb : ∀ z ∈ Complex.re ⁻¹' {u}, ‖f z‖ ≤ B) :
    ‖f z‖ ≤
      A ^ (1 - (z.re - l) / (u - l)) *
        B ^ ((z.re - l) / (u - l)) :=
  ZeroFreeRegion.hadamardThreeLines_norm_le_interp
    hul hz hd hB ha hb

/-- Public 3-4-1 contradiction criterion for high-height zero-free regions
from zeta logarithmic-derivative bounds. -/
theorem three_four_one_zero_free_high_height_of_log_deriv_bounds
    {T0 c : ℝ} {σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (hT0 : 2 ≤ T0) (hc_pos : 0 < c)
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - c / Real.log |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          realBound t)
    (hzero :
      ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - c / Real.log |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + Complex.I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + Complex.I * t) /
          riemannZeta ((σOf t : ℂ) + Complex.I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * Complex.I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ∃ c' > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c' / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.three_four_one_zero_free_high_height_of_log_deriv_bounds
    hT0 hc_pos hσ_gt hσ_le hσ_sub_pos hreal hzero htwo hmargin

/-- Public closure from the 3-4-1 logarithmic-derivative bounds to the full
classical zero-free-region target, using the compact bounded-height patch. -/
theorem classical_zero_free_region_of_log_deriv_bounds
    {T0 c : ℝ} {σOf realBound twoBound : ℝ → ℝ}
    {zeroBound : ℝ → ℝ → ℝ}
    (hT0 : 2 ≤ T0) (hc_pos : 0 < c)
    (hσ_gt : ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t)
    (hσ_le : ∀ t : ℝ, T0 ≤ |t| → σOf t ≤ 2)
    (hσ_sub_pos : ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
      β ≥ 1 - c / Real.log |t| → 0 < σOf t - β)
    (hreal :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta (σOf t : ℂ) / riemannZeta (σOf t : ℂ)).re ≤
          realBound t)
    (hzero :
      ∀ β t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 → β < 1 →
        β ≥ 1 - c / Real.log |t| → 0 < σOf t - β →
        riemannZeta ((β : ℂ) + Complex.I * t) = 0 →
        (-deriv riemannZeta ((σOf t : ℂ) + Complex.I * t) /
          riemannZeta ((σOf t : ℂ) + Complex.I * t)).re ≤ zeroBound β t)
    (htwo :
      ∀ t : ℝ, T0 ≤ |t| → 1 < σOf t → σOf t ≤ 2 →
        (-deriv riemannZeta ((σOf t : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σOf t : ℂ) + 2 * Complex.I * t)).re ≤ twoBound t)
    (hmargin :
      ∀ β t : ℝ, T0 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        3 * realBound t + 4 * zeroBound β t + twoBound t < 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_log_deriv_bounds
    hT0 hc_pos hσ_gt hσ_le hσ_sub_pos hreal hzero htwo hmargin

/-- Public height-`2` same-constant shifted-estimate closure. -/
theorem classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two
    (B : ℝ) (hB : 0 ≤ B)
    (hzero :
      ∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
        2 ≤ |t| → β < 1 →
        β ≥ 1 - c / Real.log |t| →
        0 < (1 + a / Real.log |t|) - β →
        riemannZeta ((β : ℂ) + Complex.I * t) = 0 →
        (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + Complex.I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + Complex.I * t)).re ≤
            -1 / ((1 + a / Real.log |t|) - β) +
              B * Real.log |t|)
    (htwo :
      ∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → 2 ≤ |t| →
        (-deriv riemannZeta
            ((1 + a / Real.log |t| : ℝ) + 2 * Complex.I * t) /
          riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * Complex.I * t)).re ≤
            B * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_sigma_log_shift_estimates_same_const_at_two
    B hB hzero htwo

/-- Public existential same-constant shifted-estimate closure at height `2`. -/
theorem classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ a c β t : ℝ, 0 < a → 0 < c → a ≤ Real.log 2 →
          2 ≤ |t| → β < 1 →
          β ≥ 1 - c / Real.log |t| →
          0 < (1 + a / Real.log |t|) - β →
          riemannZeta ((β : ℂ) + Complex.I * t) = 0 →
          (-deriv riemannZeta ((1 + a / Real.log |t| : ℝ) + Complex.I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + Complex.I * t)).re ≤
              -1 / ((1 + a / Real.log |t|) - β) +
                B * Real.log |t|) ∧
        (∀ a t : ℝ, 0 < a → a ≤ Real.log 2 → 2 ≤ |t| →
          (-deriv riemannZeta
              ((1 + a / Real.log |t| : ℝ) + 2 * Complex.I * t) /
            riemannZeta ((1 + a / Real.log |t| : ℝ) + 2 * Complex.I * t)).re ≤
              B * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_sigma_log_shift_estimates_same_const h

/-- Public regular-part shifted-estimate closure at height `2`. -/
theorem classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ((-deriv riemannZeta s / riemannZeta s).re +
            1 / (s.re - ρ.re)) ≤ B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
            B * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_regular_part_bound_and_two_t_bound
    B hB hregular htwo

/-- Public existential regular-part shifted-estimate closure at height `2`. -/
theorem classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ((-deriv riemannZeta s / riemannZeta s).re +
              1 / (s.re - ρ.re)) ≤ B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
            riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
              B * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_bound_and_two_t_bound h

/-- Public same-height reciprocal real-part identity. -/
theorem inv_sub_same_im_re {s ρ : ℂ} (him : ρ.im = s.im)
    (hsub : 0 < s.re - ρ.re) :
    ((s - ρ)⁻¹).re = 1 / (s.re - ρ.re) :=
  ZeroFreeRegion.inv_sub_same_im_re him hsub

/-- Public norm-bound regular-part closure at height `2`. -/
theorem classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹‖ ≤
          B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
          riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
            B * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_regular_part_norm_bound_and_two_t_bound
    B hB hregular htwo

/-- Public existential norm-bound regular-part closure at height `2`. -/
theorem classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-deriv riemannZeta s / riemannZeta s + (s - ρ)⁻¹‖ ≤
            B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-deriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t) /
            riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
              B * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_regular_part_norm_bound_and_two_t_bound h

/-- Public `-logDeriv ζ` notation form of the norm-bound regular-part closure. -/
theorem classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (B : ℝ) (hB : 0 ≤ B)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ B * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
          B * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    B hB hregular htwo

/-- Public existential `-logDeriv ζ` notation form of the norm-bound
regular-part closure. -/
theorem classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound
    (h :
      ∃ B : ℝ, 0 ≤ B ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤ B * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
            B * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_two_t_bound h

/-- Public two-coefficient `-logDeriv ζ` norm-bound regular-part closure. -/
theorem classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds
    (Bregular Btwo : ℝ) (hBregular : 0 ≤ Bregular) (hBtwo : 0 ≤ Btwo)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        (-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
          Btwo * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bounds
    Bregular Btwo hBregular hBtwo hregular htwo

/-- Public existential two-coefficient `-logDeriv ζ` norm-bound regular-part
closure. -/
theorem classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds
    (h :
      ∃ Bregular Btwo : ℝ, 0 ≤ Bregular ∧ 0 ≤ Btwo ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          (-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)).re ≤
            Btwo * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bounds h

/-- Public fully norm-bound `-logDeriv ζ` regular-part closure. -/
theorem classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    (Bregular Btwo : ℝ) (hBregular : 0 ≤ Bregular) (hBtwo : 0 ≤ Btwo)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (htwo :
      ∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
        ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)‖ ≤
          Btwo * Real.log |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    Bregular Btwo hBregular hBtwo hregular htwo

/-- Public existential fully norm-bound `-logDeriv ζ` regular-part closure. -/
theorem classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds
    (h :
      ∃ Bregular Btwo : ℝ, 0 ≤ Bregular ∧ 0 ≤ Btwo ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ σ t : ℝ, 2 ≤ |t| → 1 < σ → σ ≤ 2 →
          ‖-logDeriv riemannZeta ((σ : ℂ) + 2 * Complex.I * t)‖ ≤
            Btwo * Real.log |t|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_and_two_t_norm_bounds h

/-- Public logarithmic comparison for applying vertical estimates at height
`2t`. -/
theorem log_abs_two_mul_le_two_log_abs {t : ℝ} (ht : 2 ≤ |t|) :
    Real.log |(2 : ℝ) * t| ≤ 2 * Real.log |t| :=
  ZeroFreeRegion.log_abs_two_mul_le_two_log_abs ht

/-- Public closure from a regular-part norm estimate and a vertical-strip norm
estimate for `-logDeriv ζ`. -/
theorem classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (Bregular Bvertical : ℝ)
    (hBregular : 0 ≤ Bregular) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖-logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    Bregular Bvertical hBregular hBvertical hregular hvertical

/-- Public existential closure from a regular-part norm estimate and a
vertical-strip norm estimate for `-logDeriv ζ`. -/
theorem classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖-logDeriv riemannZeta s + (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖-logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_neg_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound h

/-- Public sign-convention wrapper from `logDeriv ζ - (s-ρ)⁻¹` regular-part
estimates to the zero-free-region closure. -/
theorem classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (Bregular Bvertical : ℝ)
    (hBregular : 0 ≤ Bregular) (hBvertical : 0 ≤ Bvertical)
    (hregular :
      ∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
        riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
        0 < s.re - ρ.re →
        ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
          Bregular * Real.log |s.im|)
    (hvertical :
      ∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
        ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    Bregular Bvertical hBregular hBvertical hregular hvertical

/-- Public existential sign-convention wrapper from `logDeriv ζ - (s-ρ)⁻¹`
regular-part estimates to the zero-free-region closure. -/
theorem classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound
    (h :
      ∃ Bregular Bvertical : ℝ, 0 ≤ Bregular ∧ 0 ≤ Bvertical ∧
        (∀ s ρ : ℂ, 2 ≤ |s.im| → s.re ∈ Set.Icc 1 2 →
          riemannZeta ρ = 0 → ρ.im = s.im → ρ.re < 1 →
          0 < s.re - ρ.re →
          ‖logDeriv riemannZeta s - (s - ρ)⁻¹‖ ≤
            Bregular * Real.log |s.im|) ∧
        (∀ z : ℂ, 2 ≤ |z.im| → z.re ∈ Set.Icc 1 2 →
          ‖logDeriv riemannZeta z‖ ≤ Bvertical * Real.log |z.im|)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_exists_logDeriv_regular_part_norm_bound_and_vertical_logDeriv_norm_bound h

/-- Public comparison between a compact-patch width and a logarithmic width. -/
theorem compact_log_width_le_of_two_le {c d t : ℝ}
    (hc : c ≤ d * Real.log 2) (hd : 0 ≤ d) (ht : 2 ≤ |t|) :
    c / Real.log |t| ≤ d :=
  ZeroFreeRegion.compact_log_width_le_of_two_le hc hd ht

/-- Public monotonicity principle for zero-free strips under width shrinkage. -/
theorem zero_free_region_mono_width
    {T0 : ℝ} {width_small width_large : ℝ → ℝ}
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width_large |s.im| → riemannZeta s ≠ 0)
    (hwidth : ∀ t : ℝ, T0 ≤ |t| → width_small |t| ≤ width_large |t|) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width_small |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.zero_free_region_mono_width hlarge hwidth

/-- Public coordinate monotonicity principle for zero-free strips under width
shrinkage. -/
theorem zero_free_region_mono_width_re_im
    {T0 : ℝ} {width_small width_large : ℝ → ℝ}
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width_large |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0)
    (hwidth : ∀ t : ℝ, T0 ≤ |t| → width_small |t| ≤ width_large |t|) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width_small |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.zero_free_region_mono_width_re_im hlarge hwidth

/-- Public high-height constant-monotonicity for the classical zero-free
width. -/
theorem classical_zero_free_region_high_height_mono_const
    {T0 csmall clarge : ℝ} (hT0 : 2 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - clarge / Real.log |s.im| → riemannZeta s ≠ 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - csmall / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_high_height_mono_const
    hT0 hc hlarge

/-- Public coordinate high-height constant-monotonicity for the classical
zero-free width. -/
theorem classical_zero_free_region_high_height_mono_const_re_im
    {T0 csmall clarge : ℝ} (hT0 : 2 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - clarge / Real.log |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - csmall / Real.log |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_high_height_mono_const_re_im
    hT0 hc hlarge

/-- Public coordinate form of Dirichlet `LFunction` nonvanishing in
`Re(s) > 1`. -/
theorem dirichlet_lfunction_ne_zero_re_im {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) {σ t : ℝ} (hσ : 1 < σ) :
    DirichletCharacter.LFunction χ ((σ : ℂ) + Complex.I * t) ≠ 0 :=
  DirichletNonvanishing.lfunction_ne_zero_re_im χ hσ

/-- Public Gamma residue at zero. -/
theorem gamma_residue_at_zero :
    Tendsto (fun s : ℂ => s * Complex.Gamma s) (𝓝[≠] 0) (𝓝 1) :=
  GammaResidue.gamma_residue_at_zero

/-- Public Gamma residue formula at the negative integers. -/
theorem gamma_residue_at_neg_natural (n : ℕ) :
    Tendsto (fun s : ℂ => (s + n) * Complex.Gamma s) (𝓝[≠] (-n : ℂ))
      (𝓝 ((-1 : ℂ) ^ n / (n.factorial : ℂ))) :=
  GammaResidue.gamma_residue_at_neg_natural n

/-- Public simple-pole package for Gamma at negative integers. -/
theorem gamma_simple_pole_at_neg_natural (n : ℕ) :
    ∃ f : ℂ → ℂ, AnalyticAt ℂ f (-n : ℂ) ∧ f (-n : ℂ) ≠ 0 ∧
      ∀ s : ℂ, (s + (n : ℂ)) ≠ 0 → Complex.Gamma s = f s / (s + n) :=
  GammaResidue.IsSimplePoleOfGamma n

/-- Public coordinate form of the classical zero-free-region target. -/
theorem classical_zero_free_region_iff_re_im :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_re_im

/-- Public forward coordinate unpacking of the classical zero-free-region
target. -/
theorem classical_zero_free_region_to_re_im
    (hclassical : ZeroFreeRegion.classical_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_to_re_im hclassical

/-- Public coordinate constructor for the classical zero-free-region target. -/
theorem classical_zero_free_region_of_re_im
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, 2 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_re_im hcoord

/-- Public compact zero-free strip next to `Re(s)=1`, valid for bounded
height. -/
theorem classical_zero_free_region_compact (T : ℝ) (hT : T ≥ 2) :
    ∃ d > 0, ∀ s : ℂ, |s.im| ≤ T →
      s.re ≥ 1 - d → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_compact T hT

/-- Public compact zero-free strip at height `T=2`. -/
theorem classical_zero_free_region_compact_at_two :
    ∃ d > 0, ∀ s : ℂ, |s.im| ≤ 2 →
      s.re ≥ 1 - d → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_compact_at_two

/-- Public coordinate form of the compact zero-free strip. -/
theorem classical_zero_free_region_compact_re_im
    (T : ℝ) (hT : T ≥ 2) :
    ∃ d > 0, ∀ β t : ℝ, |t| ≤ T →
      β ≥ 1 - d → riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_compact_re_im T hT

/-- Public coordinate compact strip restricted to the band `2 ≤ |t| ≤ T`. -/
theorem classical_zero_free_region_compact_band_re_im
    (T : ℝ) (hT : T ≥ 2) :
    ∃ d > 0, ∀ β t : ℝ, 2 ≤ |t| → |t| ≤ T →
      β ≥ 1 - d → riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_compact_band_re_im T hT

/-- Public consequence: a classical zero-free region implies nonvanishing on
the line `Re(s)=1` in its height range. -/
theorem classical_zero_free_region_on_one_line
    (hclassical : ZeroFreeRegion.classical_zero_free_region) :
    ∀ s : ℂ, 2 ≤ |s.im| → s.re = 1 → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_on_one_line hclassical

/-- Public high-height projection of the classical zero-free-region target. -/
theorem classical_zero_free_region_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hclassical : ZeroFreeRegion.classical_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_high_height T0 hT0 hclassical

/-- Public height-`3` high-height projection of the classical zero-free-region
target. -/
theorem classical_zero_free_region_high_height_at_three
    (hclassical : ZeroFreeRegion.classical_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_high_height_at_three hclassical

/-- Public high-height interface for the classical zero-free-region target. -/
theorem classical_zero_free_region_iff_high_height
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height T0 hT0

/-- Public height-`3` high-height interface for the classical zero-free-region
target. -/
theorem classical_zero_free_region_iff_high_height_at_three :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height_at_three

/-- Public bridge: the Vinogradov-Korobov target implies the classical
zero-free-region target. -/
theorem classical_zero_free_region_of_vinogradov_korobov
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov hvk

/-- Public high-height coordinate interface for the classical zero-free-region
target. -/
theorem classical_zero_free_region_iff_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0) :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height_re_im T0 hT0

/-- Public height-`3` coordinate interface for the classical zero-free-region
target, matching the Vinogradov-Korobov cutoff. -/
theorem classical_zero_free_region_iff_high_height_re_im_at_three :
    ZeroFreeRegion.classical_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.classical_zero_free_region_iff_high_height_re_im_at_three

/-- Public coordinate compact-patching theorem at the height cutoff `3`. -/
theorem compact_patch_classical_zero_free_region_re_im_at_three
    (hhigh :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_re_im_at_three hhigh

/-- Public compact-patching theorem at the height cutoff `3`. -/
theorem compact_patch_classical_zero_free_region_at_three
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_at_three hhigh

/-- Public constructor from a coordinate high-height classical-width input. -/
theorem classical_zero_free_region_of_high_height_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_high_height_re_im
    T0 hT0 hcoord

/-- Public compact patch from a high-height classical-width input. -/
theorem compact_patch_classical_zero_free_region
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region T0 hT0 hhigh

/-- Public compact patch from a high-height classical-width input stated as an
existential width theorem. -/
theorem compact_patch_classical_zero_free_region_via_width
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_via_width
    T0 hT0 hhigh

/-- Public compact patch from a coordinate high-height classical-width input. -/
theorem compact_patch_classical_zero_free_region_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0)
    (hhigh :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥ 1 - c / Real.log |t| →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_re_im T0 hT0 hhigh

/-- Public compact patch from an arbitrary high-height width function. -/
theorem compact_patch_classical_zero_free_region_of_width
    (T0 : ℝ) (hT0 : 2 ≤ T0) (width : ℝ → ℝ)
    (hregion : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥ 1 - width |s.im| → riemannZeta s ≠ 0)
    (hwidth : ∃ c > 0, ∀ t : ℝ, T0 ≤ |t| →
      c / Real.log |t| ≤ width |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_of_width
    T0 hT0 width hregion hwidth

/-- Public coordinate compact patch from an arbitrary high-height width
function. -/
theorem compact_patch_classical_zero_free_region_of_width_re_im
    (T0 : ℝ) (hT0 : 2 ≤ T0) (width : ℝ → ℝ)
    (hregion : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥ 1 - width |t| → riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0)
    (hwidth : ∃ c > 0, ∀ t : ℝ, T0 ≤ |t| →
      c / Real.log |t| ≤ width |t|) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.compact_patch_classical_zero_free_region_of_width_re_im
    T0 hT0 width hregion hwidth

/-- Public coordinate form of the Vinogradov-Korobov zero-free-region target. -/
theorem vinogradov_korobov_zero_free_region_iff_re_im :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_iff_re_im

/-- Public forward coordinate unpacking of the Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_to_re_im
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_to_re_im hvk

/-- Public coordinate constructor for the Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_of_re_im
    (hcoord :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_of_re_im hcoord

/-- Public high-height interface for the Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_high_height
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height T0 hT0 hvk

/-- Public coordinate high-height interface for the Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_high_height_re_im
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_re_im
    T0 hT0 hvk

/-- Public height-`3` high-height interface for the Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_iff_high_height_at_three :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
        s.re ≥
          1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
        riemannZeta s ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_iff_high_height_at_three

/-- Public high-height projection of the Vinogradov-Korobov target at height
`3`. -/
theorem vinogradov_korobov_zero_free_region_high_height_at_three
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥
        1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_at_three hvk

/-- Public height-`3` coordinate high-height interface for the
Vinogradov-Korobov target. -/
theorem vinogradov_korobov_zero_free_region_iff_high_height_re_im_at_three :
    ZeroFreeRegion.vinogradov_korobov_zero_free_region ↔
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_iff_high_height_re_im_at_three

/-- Public coordinate high-height projection of the Vinogradov-Korobov target
at height `3`. -/
theorem vinogradov_korobov_zero_free_region_high_height_re_im_at_three
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥
        1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_re_im_at_three
    hvk

/-- Public high-height constant-monotonicity for the Vinogradov-Korobov
width. -/
theorem vinogradov_korobov_zero_free_region_high_height_mono_const
    {T0 csmall clarge : ℝ} (hT0 : 3 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - clarge / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0) :
    ∀ s : ℂ, T0 ≤ |s.im| →
      s.re ≥
        1 - csmall / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
      riemannZeta s ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_mono_const
    hT0 hc hlarge

/-- Public coordinate high-height constant-monotonicity for the
Vinogradov-Korobov width. -/
theorem vinogradov_korobov_zero_free_region_high_height_mono_const_re_im
    {T0 csmall clarge : ℝ} (hT0 : 3 ≤ T0)
    (hc : csmall ≤ clarge)
    (hlarge : ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - clarge / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ∀ β t : ℝ, T0 ≤ |t| →
      β ≥
        1 - csmall / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_zero_free_region_high_height_mono_const_re_im
    hT0 hc hlarge

/-- Public positivity of the classical `c / log |t|` width above height `2`. -/
theorem classical_width_pos_of_two_le {c t : ℝ} (hc : 0 < c) (ht : 2 ≤ |t|) :
    0 < c / Real.log |t| :=
  ZeroFreeRegion.classical_width_pos_of_two_le hc ht

/-- Public monotonicity of the classical width in the width constant. -/
theorem classical_width_mono_const {csmall clarge t : ℝ}
    (hc : csmall ≤ clarge) (ht : 2 ≤ |t|) :
    csmall / Real.log |t| ≤ clarge / Real.log |t| :=
  ZeroFreeRegion.classical_width_mono_const hc ht

/-- Public positivity of the standard high-height choice
`1 + a / log |t|`. -/
theorem sigmaOf_log_gt_one {T0 a t : ℝ} (hT0 : 2 ≤ T0) (ha : 0 < a)
    (ht : T0 ≤ |t|) :
    1 < 1 + a / Real.log |t| :=
  ZeroFreeRegion.sigmaOf_log_gt_one hT0 ha ht

/-- Public upper bound `1 + a / log |t| ≤ 2` when `a ≤ log 2`. -/
theorem sigmaOf_log_le_two {T0 a t : ℝ} (hT0 : 2 ≤ T0)
    (ha_le : a ≤ Real.log 2) (ht : T0 ≤ |t|) :
    1 + a / Real.log |t| ≤ 2 :=
  ZeroFreeRegion.sigmaOf_log_le_two hT0 ha_le ht

/-- Public positivity of `(1 + a / log |t|) - β` for `β < 1`. -/
theorem sigmaOf_log_sub_pos {T0 a β t : ℝ} (hT0 : 2 ≤ T0) (ha : 0 < a)
    (ht : T0 ≤ |t|) (hβ_lt : β < 1) :
    0 < (1 + a / Real.log |t|) - β :=
  ZeroFreeRegion.sigmaOf_log_sub_pos hT0 ha ht hβ_lt

/-- Public local-neighborhood bound for `1 + a / log |t|`. -/
theorem sigmaOf_log_le_one_add {T0 a d t : ℝ} (hT0 : 2 ≤ T0)
    (ha_le : a ≤ d * Real.log 2) (hd : 0 ≤ d) (ht : T0 ≤ |t|) :
    1 + a / Real.log |t| ≤ 1 + d :=
  ZeroFreeRegion.sigmaOf_log_le_one_add hT0 ha_le hd ht

/-- Public real-variable negativity margin for the standard high-height choice
`σ = 1 + a / log |t|`. -/
theorem three_four_one_sigmaOf_log_margin
    {T0 a c Creal Czero Ctwo β t : ℝ}
    (hT0 : 2 ≤ T0) (ha : 0 < a) (hc : 0 < c)
    (ht : T0 ≤ |t|) (hβ_lt : β < 1)
    (hβ : β ≥ 1 - c / Real.log |t|)
    (hconst : 3 * Creal / a + 4 * Czero + Ctwo < 4 / (a + c)) :
    3 * (Creal * Real.log |t| / a)
      + 4 * (-1 / ((1 + a / Real.log |t|) - β) +
          Czero * Real.log |t|)
      + Ctwo * Real.log |t| < 0 :=
  ZeroFreeRegion.three_four_one_sigmaOf_log_margin
    hT0 ha hc ht hβ_lt hβ hconst

/-- Public real-variable choice of small constants for the standard
`σ = 1 + a / log |t|` 3-4-1 margin setup. -/
theorem exists_sigmaOf_log_margin_constants
    {C K d : ℝ} (hC_pos : 1 < C) (hC_lt : C < 4 / 3)
    (hK : 0 ≤ K) (hd : 0 < d) :
    ∃ a c : ℝ, 0 < a ∧ 0 < c ∧
      a ≤ Real.log 2 ∧ a ≤ d * Real.log 2 ∧
      3 * C / a + K < 4 / (a + c) :=
  ZeroFreeRegion.exists_sigmaOf_log_margin_constants hC_pos hC_lt hK hd

/-- Public positivity of the Vinogradov-Korobov width above height `3`. -/
theorem vinogradov_korobov_width_pos_of_three_le {c t : ℝ}
    (hc : 0 < c) (ht : 3 ≤ |t|) :
    0 <
      c / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
  ZeroFreeRegion.vinogradov_korobov_width_pos_of_three_le hc ht

/-- Public monotonicity of the Vinogradov-Korobov width in the width constant. -/
theorem vinogradov_korobov_width_mono_const {csmall clarge t : ℝ}
    (hc : csmall ≤ clarge) (ht : 3 ≤ |t|) :
    csmall / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) ≤
      clarge / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
  ZeroFreeRegion.vinogradov_korobov_width_mono_const hc ht

/-- Public pointwise width comparison showing that the Vinogradov-Korobov strip
dominates the classical `c / log |t|` strip above height `3`. -/
theorem classical_width_le_vinogradov_korobov_width {c t : ℝ}
    (hc : 0 ≤ c) (ht : 3 ≤ |t|) :
    c / Real.log |t| ≤
      c / (Real.log |t|) ^ (2 / 3 : ℝ) *
        (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
  ZeroFreeRegion.classical_width_le_vinogradov_korobov_width hc ht

/-- Public real-variable width comparison used to convert a
Vinogradov-Korobov-width high-height theorem into a classical-width one. -/
theorem vinogradov_korobov_width_comparison :
    ∀ c > 0, ∃ c' > 0, ∀ t : ℝ, 3 ≤ |t| →
      c' / Real.log |t| ≤
        c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) :=
  ZeroFreeRegion.vinogradov_korobov_width_comparison

/-- Public high-height classical-width consequence of the Vinogradov-Korobov
target, in real/imaginary coordinates. -/
theorem vinogradov_korobov_high_height_classical_zero_free_region_re_im
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
      β ≥ 1 - c / Real.log |t| →
      riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region_re_im hvk

/-- Public non-coordinate high-height classical-width consequence of the
Vinogradov-Korobov target. -/
theorem vinogradov_korobov_high_height_classical_zero_free_region
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region) :
    ∃ c > 0, ∀ s : ℂ, 3 ≤ |s.im| →
      s.re ≥ 1 - c / Real.log |s.im| → riemannZeta s ≠ 0 :=
  ZeroFreeRegion.vinogradov_korobov_high_height_classical_zero_free_region hvk

/-- Public bridge from a coordinate Vinogradov-Korobov input to the classical
zero-free-region target. -/
theorem classical_zero_free_region_of_vinogradov_korobov_re_im
    (hvk :
      ∃ c > 0, ∀ β t : ℝ, 3 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov_re_im hvk

/-- Public conditional bridge from the Vinogradov-Korobov target to the
classical zero-free-region target, parameterized by the real-variable width
comparison. -/
theorem classical_zero_free_region_of_vinogradov_korobov_with_comparison
    (hvk : ZeroFreeRegion.vinogradov_korobov_zero_free_region)
    (hcompare : ∀ c > 0, ∃ c' > 0, ∀ t : ℝ, 3 ≤ |t| →
      c' / Real.log |t| ≤
        c / (Real.log |t|) ^ (2 / 3 : ℝ) *
          (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ)) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov_with_comparison
    hvk hcompare

/-- Public bridge from an eventually valid Vinogradov-Korobov-width input to
the classical zero-free-region target. -/
theorem classical_zero_free_region_of_vinogradov_korobov_high_height
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk :
      ∃ c > 0, ∀ s : ℂ, T0 ≤ |s.im| →
        s.re ≥
          1 - c / (Real.log |s.im|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |s.im|)) ^ (-1 / 3 : ℝ) →
        riemannZeta s ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov_high_height
    T0 hT0 hvk

/-- Public bridge from an eventually valid coordinate Vinogradov-Korobov-width
input to the classical zero-free-region target. -/
theorem classical_zero_free_region_of_vinogradov_korobov_high_height_re_im
    (T0 : ℝ) (hT0 : 3 ≤ T0)
    (hvk :
      ∃ c > 0, ∀ β t : ℝ, T0 ≤ |t| →
        β ≥
          1 - c / (Real.log |t|) ^ (2 / 3 : ℝ) *
            (Real.log (Real.log |t|)) ^ (-1 / 3 : ℝ) →
        riemannZeta ((β : ℂ) + Complex.I * t) ≠ 0) :
    ZeroFreeRegion.classical_zero_free_region :=
  ZeroFreeRegion.classical_zero_free_region_of_vinogradov_korobov_high_height_re_im
    T0 hT0 hvk

/-- Public equivalence between Hardy's real `Z` zeros and zeta zeros on the
critical line. -/
theorem hardyZ_zero_iff_zeta_zero (t : ℝ) :
    HardyTheorem.hardyZ t = 0 ↔ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.hardyZ_zero_iff_zeta_zero t

/-- Public explicit formula for Hardy's real `Z` function. -/
theorem hardyZ_explicit (t : ℝ) :
    HardyTheorem.hardyZ t =
      (riemannZeta (0.5 + Complex.I * t)).re *
        Real.cos (HardyTheorem.thetaPhase t)
      - (riemannZeta (0.5 + Complex.I * t)).im *
        Real.sin (HardyTheorem.thetaPhase t) :=
  HardyTheorem.hardyZ_explicit t

/-- Public value of the Hardy phase at zero. -/
theorem thetaPhase_zero :
    HardyTheorem.thetaPhase 0 =
      Complex.arg (Complex.Gamma (1 / 4 : ℂ)) :=
  HardyTheorem.thetaPhase_zero

/-- Public forward zero transfer from zeta to Hardy `Z`. -/
theorem zeta_zero_implies_hardyZ_zero
    (t : ℝ) (h : riemannZeta (0.5 + Complex.I * t) = 0) :
    HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.zeta_zero_implies_hardyZ_zero t h

/-- Public reverse zero transfer from Hardy `Z` to zeta on the critical line. -/
theorem hardyZ_zero_implies_zeta_zero
    (t : ℝ) (h : HardyTheorem.hardyZ t = 0) :
    riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.hardyZ_zero_implies_zeta_zero t h

/-- Public conjugation identity for completed zeta in the half-plane
`Re(s)>1`. -/
theorem completedRiemannZeta_conj_eq_of_one_lt_re {s : ℂ} (hs : 1 < s.re) :
    completedRiemannZeta (conj s) = conj (completedRiemannZeta s) :=
  HardyTheorem.completedRiemannZeta_conj_eq_of_one_lt_re hs

/-- Public conjugation identity for the entire completed zeta variant. -/
theorem completedRiemannZeta₀_conj_eq (s : ℂ) :
    completedRiemannZeta₀ (conj s) = conj (completedRiemannZeta₀ s) :=
  HardyTheorem.completedRiemannZeta₀_conj_eq s

/-- Public reality statement for completed zeta on the critical line. -/
theorem completedRiemannZeta_critical_line_real (t : ℝ) :
    ∃ r : ℝ, completedRiemannZeta ((1 / 2 : ℂ) + Complex.I * t) = r :=
  HardyTheorem.completedRiemannZeta_critical_line_real t

/-- Public polar-coordinate real/imaginary formula for the Gamma factor on the
critical line. -/
theorem Gammaℝ_re_im_arg (t : ℝ) :
    (Gammaℝ ((1 / 2 : ℂ) + Complex.I * t)).re =
        ‖Gammaℝ ((1 / 2 : ℂ) + Complex.I * t)‖ *
          Real.cos (HardyTheorem.thetaPhase t) ∧
      (Gammaℝ ((1 / 2 : ℂ) + Complex.I * t)).im =
        ‖Gammaℝ ((1 / 2 : ℂ) + Complex.I * t)‖ *
          Real.sin (HardyTheorem.thetaPhase t) :=
  HardyTheorem.Gammaℝ_re_im_arg t

/-- Public equality of the Hardy-Z zero set and the critical-line zeta-zero
set. -/
theorem hardyZ_zero_set_eq_critical_line_zeta_zero_set :
    {t : ℝ | HardyTheorem.hardyZ t = 0} =
      {t : ℝ | riemannZeta (0.5 + Complex.I * t) = 0} :=
  HardyTheorem.hardyZ_zero_set_eq_critical_line_zeta_zero_set

/-- Public finiteness equivalence for Hardy-Z and zeta zeros on the critical
line. -/
theorem hardyZ_zero_set_finite_iff_critical_line_zeta_zero_set_finite :
    {t : ℝ | HardyTheorem.hardyZ t = 0}.Finite ↔
      {t : ℝ | riemannZeta (0.5 + Complex.I * t) = 0}.Finite :=
  HardyTheorem.hardyZ_zero_set_finite_iff_critical_line_zeta_zero_set_finite

/-- Public continuity theorem for Hardy's real `Z` function. -/
theorem hardyZ_continuous : Continuous HardyTheorem.hardyZ :=
  HardyTheorem.hardyZ_continuous

/-- Public sign-change helper for negating weighted integrals. -/
theorem weightedIntegralOf_neg (f : ℝ → ℝ) (n : ℕ) (T : ℝ) :
    HardyTheorem.weightedIntegralOf (fun t => -f t) n T =
      -HardyTheorem.weightedIntegralOf f n T :=
  HardyTheorem.weightedIntegralOf_neg f n T

/-- Public nonnegativity of Hardy's polynomial weight. -/
theorem weightFunction_nonneg (n : ℕ) (t : ℝ) :
    0 ≤ HardyTheorem.weightFunction n t :=
  HardyTheorem.weightFunction_nonneg n t

/-- Public positivity consequence for weighted Hardy integrals under eventual
positive sign and tail dominance. -/
theorem weighted_integral_eventually_positive_of_hardyZ_positive
    (n : ℕ) (h_pos : ∀ᶠ t in atTop, HardyTheorem.hardyZ t > 0)
    (h_tail : HardyTheorem.weightedIntegralOf_tail_dominates
      HardyTheorem.hardyZ n) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegral n T > 0 :=
  HardyTheorem.weighted_integral_eventually_positive_of_hardyZ_positive
    n h_pos h_tail

/-- Public negativity consequence for weighted Hardy integrals under eventual
negative sign and signed tail dominance. -/
theorem weighted_integral_eventually_negative_of_hardyZ_negative
    (n : ℕ) (h_neg : ∀ᶠ t in atTop, HardyTheorem.hardyZ t < 0)
    (h_tail : HardyTheorem.weightedIntegralOf_tail_dominates
      (fun t => -HardyTheorem.hardyZ t) n) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegral n T < 0 :=
  HardyTheorem.weighted_integral_eventually_negative_of_hardyZ_negative
    n h_neg h_tail

/-- Public structure lemma: bounded Hardy-Z zeros force eventual constant sign
at positive height. -/
theorem hardyZ_eventually_const_sign_of_bounded_zeros
    (hbounded : Bornology.IsBounded {t : ℝ | HardyTheorem.hardyZ t = 0}) :
    (∀ᶠ t in atTop, HardyTheorem.hardyZ t > 0) ∨
      (∀ᶠ t in atTop, HardyTheorem.hardyZ t < 0) :=
  HardyTheorem.hardyZ_eventually_const_sign_of_bounded_zeros hbounded

/-- Public structure lemma: finitely many Hardy-Z zeros force eventual constant
sign at positive height. -/
theorem hardyZ_eventually_const_sign_of_finite_zeros
    (hfinite : {t : ℝ | HardyTheorem.hardyZ t = 0}.Finite) :
    (∀ᶠ t in atTop, HardyTheorem.hardyZ t > 0) ∨
      (∀ᶠ t in atTop, HardyTheorem.hardyZ t < 0) :=
  HardyTheorem.hardyZ_eventually_const_sign_of_finite_zeros hfinite

/-- Public structure lemma: finitely many zeta zeros on the critical line force
Hardy-Z eventual constant sign at positive height. -/
theorem hardyZ_eventually_const_sign_of_finite_critical_line_zeros
    (hfinite : {t : ℝ | riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    (∀ᶠ t in atTop, HardyTheorem.hardyZ t > 0) ∨
      (∀ᶠ t in atTop, HardyTheorem.hardyZ t < 0) :=
  HardyTheorem.hardyZ_eventually_const_sign_of_finite_critical_line_zeros hfinite

/-- Public packaging equivalence: the two signed Hardy moments are exactly the
first two signed integral-asymptotic targets. -/
theorem hardy_two_signed_moments_target_iff_integral_asymptotic_one_two :
    HardyTheorem.hardy_two_signed_moments_target ↔
      HardyTheorem.integral_asymptotic_target 1 ∧
        HardyTheorem.integral_asymptotic_target 2 :=
  HardyTheorem.hardy_two_signed_moments_target_iff_integral_asymptotic_one_two

/-- Public constructor for a weighted-integral asymptotic target from its
positive leading constant and asymptotic equivalence. -/
theorem integral_asymptotic_target_of_asymptotic {n : ℕ}
    (hn : 1 ≤ n) {A : ℝ} (hA : 0 < A)
    (hasymp :
      (fun T => HardyTheorem.weightedIntegral n T) ~[atTop]
        (fun T => ((-1 : ℝ) ^ n * A) *
          T ^ ((2 * n : ℝ) + 1 / 4))) :
    HardyTheorem.integral_asymptotic_target n :=
  HardyTheorem.integral_asymptotic_target_of_asymptotic hn hA hasymp

/-- Public lower-bound destructor for weighted-integral asymptotic targets. -/
theorem integral_asymptotic_target_ge_one {n : ℕ}
    (h : HardyTheorem.integral_asymptotic_target n) : 1 ≤ n :=
  HardyTheorem.integral_asymptotic_target_ge_one h

/-- Public positive-leading-constant destructor for weighted-integral
asymptotic targets. -/
theorem exists_positive_asymptotic_of_integral_asymptotic_target {n : ℕ}
    (h : HardyTheorem.integral_asymptotic_target n) :
    ∃ A : ℝ, 0 < A ∧
      (fun T => HardyTheorem.weightedIntegral n T) ~[atTop]
        (fun T => ((-1 : ℝ) ^ n * A) *
          T ^ ((2 * n : ℝ) + 1 / 4)) :=
  HardyTheorem.exists_positive_asymptotic_of_integral_asymptotic_target h

/-- Public unfolded form of the first Hardy weighted-integral asymptotic
target. -/
theorem integral_asymptotic_target_one_iff :
    HardyTheorem.integral_asymptotic_target 1 ↔
      ∃ A : ℝ, 0 < A ∧
        (fun T => HardyTheorem.weightedIntegral 1 T) ~[atTop]
          (fun T => -A * T ^ ((2 : ℝ) + 1 / 4)) :=
  HardyTheorem.integral_asymptotic_target_one_iff

/-- Public unfolded form of the second Hardy weighted-integral asymptotic
target. -/
theorem integral_asymptotic_target_two_iff :
    HardyTheorem.integral_asymptotic_target 2 ↔
      ∃ A : ℝ, 0 < A ∧
        (fun T => HardyTheorem.weightedIntegral 2 T) ~[atTop]
          (fun T => A * T ^ ((2 * 2 : ℝ) + 1 / 4)) :=
  HardyTheorem.integral_asymptotic_target_two_iff

/-- Public bridge from the two signed Hardy moments to the first integral
asymptotic target. -/
theorem integral_asymptotic_one_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.integral_asymptotic_target 1 :=
  HardyTheorem.integral_asymptotic_one_of_two_signed_moments h

/-- Public bridge from the two signed Hardy moments to the second integral
asymptotic target. -/
theorem integral_asymptotic_two_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.integral_asymptotic_target 2 :=
  HardyTheorem.integral_asymptotic_two_of_two_signed_moments h

/-- Public packaging lemma from the first two integral asymptotics to the two
signed Hardy moment target. -/
theorem hardy_two_signed_moments_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_two_signed_moments_target :=
  HardyTheorem.hardy_two_signed_moments_of_integral_asymptotic_one_two h1 h2

/-- Public tail-dominance bridge from divergence of a weighted integral to
`atTop`. -/
theorem weightedIntegralOf_tail_dominates_of_tendsto_atTop
    {f : ℝ → ℝ} {n : ℕ}
    (h : Tendsto (fun T => HardyTheorem.weightedIntegralOf f n T) atTop atTop) :
    HardyTheorem.weightedIntegralOf_tail_dominates f n :=
  HardyTheorem.weightedIntegralOf_tail_dominates_of_tendsto_atTop h

/-- Public tail-dominance bridge for the negated function from divergence to
`atBot`. -/
theorem weightedIntegralOf_tail_dominates_neg_of_tendsto_atBot
    {f : ℝ → ℝ} {n : ℕ}
    (h : Tendsto (fun T => HardyTheorem.weightedIntegralOf f n T) atTop atBot) :
    HardyTheorem.weightedIntegralOf_tail_dominates (fun t => -f t) n :=
  HardyTheorem.weightedIntegralOf_tail_dominates_neg_of_tendsto_atBot h

/-- Public eventual-positivity consequence of tail dominance. -/
theorem weightedIntegralOf_eventually_positive_of_tail_dominates
    (f : ℝ → ℝ) (n : ℕ) (hf : Continuous f)
    (hpos : ∀ᶠ t in atTop, f t > 0)
    (htail : HardyTheorem.weightedIntegralOf_tail_dominates f n) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegralOf f n T > 0 :=
  HardyTheorem.weightedIntegralOf_eventually_positive_of_tail_dominates
    f n hf hpos htail

/-- Public eventual-negativity consequence of tail dominance for the negated
function. -/
theorem weightedIntegralOf_eventually_negative_of_neg_tail_dominates
    (f : ℝ → ℝ) (n : ℕ) (hf : Continuous f)
    (hneg : ∀ᶠ t in atTop, f t < 0)
    (htail : HardyTheorem.weightedIntegralOf_tail_dominates (fun t => -f t) n) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegralOf f n T < 0 :=
  HardyTheorem.weightedIntegralOf_eventually_negative_of_neg_tail_dominates
    f n hf hneg htail

/-- Public bounded-below consequence for weighted Hardy integrals under
eventual positivity of `Z`. -/
theorem weightedIntegral_eventually_bddBelow_of_hardyZ_positive
    (n : ℕ) (hpos : ∀ᶠ t in atTop, HardyTheorem.hardyZ t > 0) :
    ∃ C : ℝ, ∀ᶠ T in atTop, C ≤ HardyTheorem.weightedIntegral n T :=
  HardyTheorem.weightedIntegral_eventually_bddBelow_of_hardyZ_positive n hpos

/-- Public bounded-above consequence for weighted Hardy integrals under
eventual negativity of `Z`. -/
theorem weightedIntegral_eventually_bddAbove_of_hardyZ_negative
    (n : ℕ) (hneg : ∀ᶠ t in atTop, HardyTheorem.hardyZ t < 0) :
    ∃ C : ℝ, ∀ᶠ T in atTop, HardyTheorem.weightedIntegral n T ≤ C :=
  HardyTheorem.weightedIntegral_eventually_bddAbove_of_hardyZ_negative n hneg

/-- Public consequence of the two signed Hardy moments: the first weighted
integral tends to `atBot`. -/
theorem weightedIntegral_one_tendsto_atBot_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => HardyTheorem.weightedIntegral 1 T) atTop atBot :=
  HardyTheorem.weightedIntegral_one_tendsto_atBot_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the first weighted
integral is eventually negative. -/
theorem weightedIntegral_one_eventually_negative_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, HardyTheorem.weightedIntegral 1 T < 0 :=
  HardyTheorem.weightedIntegral_one_eventually_negative_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the second weighted
integral tends to `atTop`. -/
theorem weightedIntegral_two_tendsto_atTop_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    Tendsto (fun T : ℝ => HardyTheorem.weightedIntegral 2 T) atTop atTop :=
  HardyTheorem.weightedIntegral_two_tendsto_atTop_of_two_signed_moments h

/-- Public consequence of the two signed Hardy moments: the second weighted
integral is eventually positive. -/
theorem weightedIntegral_two_eventually_positive_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    ∀ᶠ T in atTop, 0 < HardyTheorem.weightedIntegral 2 T :=
  HardyTheorem.weightedIntegral_two_eventually_positive_of_two_signed_moments h

/-- Public tail-dominance consequence for `-hardyZ` from the first signed
Hardy moment. -/
theorem weightedIntegralOf_neg_hardyZ_one_tail_dominates_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.weightedIntegralOf_tail_dominates
      (fun t => -HardyTheorem.hardyZ t) 1 :=
  HardyTheorem.weightedIntegralOf_neg_hardyZ_one_tail_dominates_of_two_signed_moments h

/-- Public tail-dominance consequence for `hardyZ` from the second signed
Hardy moment. -/
theorem weightedIntegralOf_hardyZ_two_tail_dominates_of_two_signed_moments
    (h : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.weightedIntegralOf_tail_dominates HardyTheorem.hardyZ 2 :=
  HardyTheorem.weightedIntegralOf_hardyZ_two_tail_dominates_of_two_signed_moments h

/-- Public contradiction: finite Hardy-Z zeros are incompatible with the two
signed Hardy moment asymptotics. -/
theorem finite_zeros_contradiction_of_two_signed_moments
    (hfinite : {t : ℝ | HardyTheorem.hardyZ t = 0}.Finite)
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    False :=
  HardyTheorem.finite_zeros_contradiction_of_two_signed_moments hfinite hmom

/-- Public contradiction package with explicit tail-dominance hypotheses. -/
theorem finite_zeros_contradiction_of_two_signed_moments_and_tail_dominance
    (hfinite : {t : ℝ | HardyTheorem.hardyZ t = 0}.Finite)
    (hmom : HardyTheorem.hardy_two_signed_moments_target)
    (htail_pos : HardyTheorem.weightedIntegralOf_tail_dominates HardyTheorem.hardyZ 1)
    (htail_neg :
      HardyTheorem.weightedIntegralOf_tail_dominates
        (fun t => -HardyTheorem.hardyZ t) 2) :
    False :=
  HardyTheorem.finite_zeros_contradiction_of_two_signed_moments_and_tail_dominance
    hfinite hmom htail_pos htail_neg

/-- Public equivalence between Hardy's infinite-zero target and infinitude of
Hardy `Z` zeros. -/
theorem hardy_theorem_target_iff_hardyZ_zero_set_infinite :
    HardyTheorem.hardy_theorem_target ↔
      {t : ℝ | HardyTheorem.hardyZ t = 0}.Infinite :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_zero_set_infinite

/-- Public consequence: Hardy's infinite-zero target gives at least one
critical-line zero. -/
theorem exists_zero_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_hardy_theorem_target h

/-- Public consequence: the first two signed Hardy moments give at least one
critical-line zero. -/
theorem exists_zero_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_two_signed_moments hmom

/-- Public consequence: the first two Hardy integral asymptotics give at least
one critical-line zero. -/
theorem exists_zero_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_integral_asymptotic_one_two h1 h2

/-- Public consequence: Hardy's infinite-zero target gives at least one complex
critical-line zero. -/
theorem exists_complex_zero_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_hardy_theorem_target h

/-- Public consequence: Hardy's infinite-zero target gives at least one
nontrivial zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_hardy_theorem_target h

/-- Public consequence: the first two signed Hardy moments give at least one
complex critical-line zero. -/
theorem exists_complex_zero_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom)

/-- Public consequence: the first two signed Hardy moments give at least one
nontrivial zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_two_signed_moments hmom)

/-- Public consequence: the first two Hardy integral asymptotics give at least
one complex critical-line zero. -/
theorem exists_complex_zero_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2)

/-- Public consequence: the first two Hardy integral asymptotics give at least
one nontrivial zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_hardy_theorem_target
    (HardyTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2)

/-- Public consequence: the Hardy--Littlewood lower-bound target gives at least
one real critical-line zero. -/
theorem exists_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_zero_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public consequence: the Hardy--Littlewood lower-bound target gives at least
one nonnegative real critical-line zero. -/
theorem exists_nonnegative_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∃ t : ℝ, 0 ≤ t ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_nonnegative_zero_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public consequence: the Hardy--Littlewood lower-bound target gives at least
one complex critical-line zero. -/
theorem exists_complex_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public consequence: the Hardy--Littlewood lower-bound target gives at least
one nontrivial zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public consequence: Selberg's positive-proportion target gives at least
one real critical-line zero. -/
theorem exists_zero_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_zero_on_critical_line_of_selberg_zero_proportion h

/-- Public consequence: Selberg's positive-proportion target gives at least
one nonnegative real critical-line zero. -/
theorem exists_nonnegative_zero_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ t : ℝ, 0 ≤ t ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_nonnegative_zero_on_critical_line_of_selberg_zero_proportion h

/-- Public consequence: Selberg's positive-proportion target gives at least one
complex critical-line zero. -/
theorem exists_complex_zero_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_selberg_zero_proportion h

/-- Public consequence: Selberg's positive-proportion target gives at least one
nontrivial zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_selberg_zero_proportion h

/-- Public bridge from Hardy's unbounded-height target to infinitely many
critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_unbounded h

/-- Public bridge between one-sided and absolute-height Hardy unbounded targets. -/
theorem hardy_zeros_unbounded_iff_abs_unbounded :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded

/-- Public HardyZ form of the positive-height unbounded target. -/
theorem hardy_zeros_unbounded_target_iff_hardyZ_unbounded :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_zeros_unbounded_target_iff_hardyZ_unbounded

/-- Public eventual-existence form of the positive-height Hardy zero target. -/
theorem hardy_zeros_unbounded_target_iff_eventually_exists :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      ∀ᶠ T in atTop,
        ∃ t : ℝ, T ≤ t ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.hardy_zeros_unbounded_target_iff_eventually_exists

/-- Public HardyZ form of the absolute-height unbounded target. -/
theorem hardy_zeros_abs_unbounded_target_iff_hardyZ_abs_unbounded :
    HardyTheorem.hardy_zeros_abs_unbounded_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_zeros_abs_unbounded_target_iff_hardyZ_abs_unbounded

/-- Public eventual-existence form of the absolute-height Hardy zero target. -/
theorem hardy_zeros_abs_unbounded_target_iff_eventually_exists_abs :
    HardyTheorem.hardy_zeros_abs_unbounded_target ↔
      ∀ᶠ T in atTop,
        ∃ t : ℝ, T ≤ |t| ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.hardy_zeros_abs_unbounded_target_iff_eventually_exists_abs

/-- Public bridge from one-sided unbounded Hardy zeros to absolute-height
unbounded Hardy zeros. -/
theorem hardy_zeros_abs_unbounded_of_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_unbounded h

/-- Public bridge from Hardy's one-sided unbounded target to the infinite-zero
target. -/
theorem hardy_theorem_target_of_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_unbounded h

/-- Public bridge from Hardy's absolute-height unbounded target to the
infinite-zero target. -/
theorem hardy_theorem_target_of_abs_unbounded
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_abs_unbounded h

/-- Public extraction of a nonnegative critical-line zero from Hardy's
one-sided unbounded target. -/
theorem exists_nonnegative_zero_on_critical_line_of_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    ∃ t : ℝ, 0 ≤ t ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_nonnegative_zero_on_critical_line_of_unbounded h

/-- Public extraction of a critical-line zero from Hardy's one-sided unbounded
target. -/
theorem exists_zero_on_critical_line_of_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_unbounded h

/-- Public extraction of a critical-line zero from Hardy's absolute-height
unbounded target. -/
theorem exists_zero_on_critical_line_of_abs_unbounded
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_on_critical_line_of_abs_unbounded h

/-- Public symmetry of critical-line zeta zeros under height negation. -/
theorem critical_line_zeta_zero_neg_height (t : ℝ)
    (h : riemannZeta (0.5 + Complex.I * t) = 0) :
    riemannZeta (0.5 + Complex.I * (-t)) = 0 :=
  HardyTheorem.critical_line_zeta_zero_neg_height t h

/-- Public bridge from absolute-height unboundedness to one-sided
unboundedness, parameterized by height-negation symmetry. -/
theorem hardy_zeros_unbounded_of_abs_unbounded_of_neg_symm
    (hsymm : ∀ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 →
      riemannZeta (0.5 + Complex.I * (-t)) = 0)
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_abs_unbounded_of_neg_symm hsymm h

/-- Public equivalence between one-sided and absolute-height Hardy
unboundedness under height-negation symmetry. -/
theorem hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm
    (hsymm : ∀ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 →
      riemannZeta (0.5 + Complex.I * (-t)) = 0) :
    HardyTheorem.hardy_zeros_unbounded_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_iff_abs_unbounded_of_neg_symm hsymm

/-- Public equivalence between Hardy's infinite-zero target and the
absolute-height unbounded target, using the local finiteness of zeta zeros in
bounded height. -/
theorem hardy_theorem_target_iff_abs_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_theorem_target_iff_abs_unbounded

/-- Public equivalence between Hardy's infinite-zero target and the
positive-height unbounded target, using symmetry on the critical line. -/
theorem hardy_theorem_target_iff_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_theorem_target_iff_unbounded

/-- Public unconditional Hardy-Z absolute-height form of Hardy's infinite-zero
target. -/
theorem hardy_theorem_target_iff_hardyZ_abs_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  PrimeNumberTheorem.hardy_theorem_target_iff_hardyZ_abs_unbounded

/-- Public unconditional Hardy-Z positive-height form of Hardy's infinite-zero
target. -/
theorem hardy_theorem_target_iff_hardyZ_unbounded :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ HardyTheorem.hardyZ t = 0 :=
  PrimeNumberTheorem.hardy_theorem_target_iff_hardyZ_unbounded

/-- Public bounded-strip version of the equivalence between Hardy's infinite
zero target and absolute-height unbounded zeros. -/
theorem hardy_theorem_target_iff_abs_unbounded_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_theorem_target_iff_abs_unbounded_of_bounded_strips hstrip

/-- Public bounded-strip version of the equivalence between Hardy's infinite
zero target and positive-height unbounded zeros. -/
theorem hardy_theorem_target_iff_unbounded_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    HardyTheorem.hardy_theorem_target ↔
      HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_theorem_target_iff_unbounded_of_bounded_strips hstrip

/-- Public bounded-strip Hardy-Z form of the unbounded-height equivalence. -/
theorem hardy_theorem_target_iff_hardyZ_unbounded_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ t ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_unbounded_of_bounded_strips hstrip

/-- Public bounded-strip Hardy-Z form of the absolute-height unbounded
equivalence. -/
theorem hardy_theorem_target_iff_hardyZ_abs_unbounded_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_abs_unbounded_of_bounded_strips
    hstrip

/-- Public bounded-strip Hardy-Z zero-set form of the absolute-height
unbounded equivalence. -/
theorem hardy_theorem_target_iff_hardyZ_abs_unbounded_of_hardyZ_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧ HardyTheorem.hardyZ t = 0}.Finite) :
    HardyTheorem.hardy_theorem_target ↔
      ∀ T : ℝ, ∃ t : ℝ, T ≤ |t| ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.hardy_theorem_target_iff_hardyZ_abs_unbounded_of_hardyZ_bounded_strips
    hstrip

/-- Public bounded-strip bridge from Hardy's infinite-zero target to
absolute-height unbounded zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_theorem_target_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_hardy_theorem_target_of_bounded_strips
    hstrip h

/-- Public bounded-strip bridge from Hardy's infinite-zero target to
positive-height unbounded zeros. -/
theorem hardy_zeros_unbounded_of_hardy_theorem_target_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_hardy_theorem_target_of_bounded_strips
    hstrip h

/-- Public bounded-strip bridge from the first two signed Hardy moments to
absolute-height unbounded critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments_of_bounded_strips
    hstrip hmom

/-- Public bounded-strip bridge from the first two Hardy integral asymptotics
to absolute-height unbounded critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two_of_bounded_strips
    hstrip h1 h2

/-- Public bounded-strip bridge from the first two signed Hardy moments to
one-sided unbounded critical-line zeros. -/
theorem hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_two_signed_moments_of_bounded_strips
    hstrip hmom

/-- Public bounded-strip bridge from the first two Hardy integral asymptotics
to one-sided unbounded critical-line zeros. -/
theorem hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two_of_bounded_strips
    hstrip h1 h2

/-- Public bridge from Hardy's infinite-zero target to arbitrarily large
absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_hardy_theorem_target h

/-- Public bridge from Hardy's infinite-zero target to arbitrarily large
positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_theorem_target h

/-- Public bridge from the first two signed Hardy moment targets to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_two_signed_moments hmom

/-- Public bridge from the first two signed Hardy moments plus explicit tail
dominance hypotheses to Hardy's infinite-zero target. -/
theorem hardy_theorem_target_of_two_signed_moments_and_tail_dominance
    (hmom : HardyTheorem.hardy_two_signed_moments_target)
    (htail_pos : HardyTheorem.weightedIntegralOf_tail_dominates
      HardyTheorem.hardyZ 1)
    (htail_neg : HardyTheorem.weightedIntegralOf_tail_dominates
      (fun t => -HardyTheorem.hardyZ t) 2) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_two_signed_moments_and_tail_dominance
    hmom htail_pos htail_neg

/-- Public bridge from the first two Hardy integral asymptotics to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_integral_asymptotic_one_two h1 h2

/-- Public bridge from the first two signed Hardy moments to arbitrarily large
absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_two_signed_moments hmom

/-- Public bridge from the first two signed Hardy moments to arbitrarily large
positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_two_signed_moments hmom

/-- Public bridge from the first two Hardy integral asymptotics to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_integral_asymptotic_one_two
    h1 h2

/-- Public bridge from the first two Hardy integral asymptotics to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_integral_asymptotic_one_two
    h1 h2

/-- Public bridge from Hardy's absolute-height unbounded target to infinitely
many critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_abs_unbounded
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line
    (HardyTheorem.hardy_theorem_target_of_abs_unbounded h)

/-- Public bridge from Hardy's infinite-zero target to infinitely many complex
critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line h

/-- Public bridge from the first two signed Hardy moments to infinitely many
complex critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_two_signed_moments hmom

/-- Public bridge from the first two Hardy integral asymptotics to infinitely
many complex critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_integral_asymptotic_one_two
    h1 h2

/-- Public eventually-linear form of the Hardy--Littlewood lower-bound target. -/
theorem hardy_littlewood_lower_bound_target_iff_eventually_linear_lower_bound :
    HardyTheorem.hardy_littlewood_lower_bound_target ↔
      ∃ C > 0, ∀ᶠ T in atTop,
        (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥ C * T :=
  HardyTheorem.hardy_littlewood_lower_bound_target_iff_eventually_linear_lower_bound

/-- Public eventually-logarithmic form of Selberg's positive-proportion target. -/
theorem selberg_zero_proportion_target_iff_eventually_log_lower_bound :
    HardyTheorem.selberg_zero_proportion_target ↔
      ∃ c > 0, ∀ᶠ T in atTop,
        (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
          c * (T / (2 * Real.pi) * Real.log T) :=
  HardyTheorem.selberg_zero_proportion_target_iff_eventually_log_lower_bound

/-- Public eventual domination of any fixed natural count from the
Hardy--Littlewood lower-bound target. -/
theorem eventually_nat_lt_zeroCountOnCriticalLine_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) (N : ℕ) :
    ∀ᶠ T in atTop, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.eventually_nat_lt_zeroCountOnCriticalLine_of_hardy_littlewood_lower_bound
    h N

/-- Public eventual positivity of the critical-line zero count from the
Hardy--Littlewood lower-bound target. -/
theorem eventually_zeroCountOnCriticalLine_pos_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ᶠ T in atTop, 0 < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.eventually_zeroCountOnCriticalLine_pos_of_hardy_littlewood_lower_bound h

/-- Public bridge: Selberg's positive-proportion target implies the
Hardy--Littlewood lower-bound target. -/
theorem hardy_littlewood_lower_bound_target_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_littlewood_lower_bound_target :=
  HardyTheorem.hardy_littlewood_lower_bound_target_of_selberg_zero_proportion h

/-- Public eventual linear lower-bound consequence of Selberg's
positive-proportion target. -/
theorem eventually_linear_lower_bound_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∃ C > 0, ∀ᶠ T in atTop,
      (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥ C * T :=
  HardyTheorem.eventually_linear_lower_bound_of_selberg_zero_proportion h

/-- Public eventual domination of any fixed natural count from Selberg's
positive-proportion target. -/
theorem eventually_nat_lt_zeroCountOnCriticalLine_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) (N : ℕ) :
    ∀ᶠ T in atTop, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.eventually_nat_lt_zeroCountOnCriticalLine_of_selberg_zero_proportion
    h N

/-- Public eventual positivity of the critical-line zero count from Selberg's
positive-proportion target. -/
theorem eventually_zeroCountOnCriticalLine_pos_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ᶠ T in atTop, 0 < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.eventually_zeroCountOnCriticalLine_pos_of_selberg_zero_proportion h

/-- Public bridge from the Hardy--Littlewood lower-bound target to infinitely
many complex critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public bridge from Selberg's positive-proportion target to infinitely many
complex critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_selberg_zero_proportion h

/-- Public bridge from Hardy's infinite-zero target to infinitely many
nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_hardy_theorem_target
    (h : HardyTheorem.hardy_theorem_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line h

/-- Public bridge from the first two signed Hardy moments to infinitely many
nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_two_signed_moments
    (hmom : HardyTheorem.hardy_two_signed_moments_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_two_signed_moments
    hmom

/-- Public bridge from the first two Hardy integral asymptotics to infinitely
many nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_integral_asymptotic_one_two
    (h1 : HardyTheorem.integral_asymptotic_target 1)
    (h2 : HardyTheorem.integral_asymptotic_target 2) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_integral_asymptotic_one_two
    h1 h2

/-- Public bridge from Hardy's unbounded-height target to infinitely many
nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_hardy_unbounded
    (h : HardyTheorem.hardy_zeros_unbounded_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_unbounded h

/-- Public bridge from Hardy's absolute-height unbounded target to infinitely
many nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_hardy_abs_unbounded
    (h : HardyTheorem.hardy_zeros_abs_unbounded_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_abs_unbounded h

/-- Public bridge from Hardy--Littlewood's lower-bound target to infinitely many
nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_hardy_littlewood_lower_bound h

/-- Public bridge from Selberg's positive-proportion target to infinitely many
nontrivial critical-line zeros. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_selberg_zero_proportion h

/-- Public interval-zero consequence of the Hardy--Littlewood lower-bound
target. -/
theorem eventually_exists_zero_on_critical_line_interval_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.eventually_exists_zero_on_critical_line_interval_of_hardy_littlewood_lower_bound h

/-- Public interval-zero consequence of Selberg's positive-proportion target. -/
theorem eventually_exists_zero_on_critical_line_interval_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.eventually_exists_zero_on_critical_line_interval_of_selberg_zero_proportion h

/-- Public Hardy-Z interval-zero consequence of the Hardy--Littlewood
lower-bound target. -/
theorem eventually_exists_hardyZ_zero_interval_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ᶠ T in atTop, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  KnownResults.eventually_exists_hardyZ_zero_interval_of_hardy_littlewood_lower_bound h

/-- Public Hardy-Z interval-zero consequence of Selberg's positive-proportion
target. -/
theorem eventually_exists_hardyZ_zero_interval_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ᶠ T in atTop, ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  KnownResults.eventually_exists_hardyZ_zero_interval_of_selberg_zero_proportion h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
arbitrarily large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
arbitrarily large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound h

/-- Public bridge from Hardy--Littlewood's linear lower-bound target to
Hardy's infinite-zero target. -/
theorem hardy_theorem_target_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_hardy_littlewood_lower_bound h

/-- Public bridge from Selberg's positive-proportion target to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion h

/-- Public bridge from Selberg's positive-proportion target to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion h

/-- Public bridge from Selberg's positive-proportion target to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_selberg_zero_proportion h

/-- Public bounded-strip bridge from Hardy--Littlewood's linear lower-bound
target to absolute-height unbounded critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips
    hstrip h

/-- Public bounded-strip bridge from Hardy--Littlewood's linear lower-bound
target to one-sided unbounded critical-line zeros. -/
theorem hardy_zeros_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_hardy_littlewood_lower_bound_of_bounded_strips
    hstrip h

/-- Public bounded-strip bridge from Selberg's positive-proportion target to
absolute-height unbounded critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_selberg_zero_proportion_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  HardyTheorem.hardy_zeros_abs_unbounded_of_selberg_zero_proportion_of_bounded_strips
    hstrip h

/-- Public bounded-strip bridge from Selberg's positive-proportion target to
one-sided unbounded critical-line zeros. -/
theorem hardy_zeros_unbounded_of_selberg_zero_proportion_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧
        riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : HardyTheorem.selberg_zero_proportion_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  HardyTheorem.hardy_zeros_unbounded_of_selberg_zero_proportion_of_bounded_strips
    hstrip h

/-- Public equivalence between the Conrey-style 40-percent target and the
project's Selberg positive-proportion target. -/
theorem conrey_40_percent_zeros_on_critical_line_target_iff_selberg :
    KnownResults.conrey_40_percent_zeros_on_critical_line_target ↔
      HardyTheorem.selberg_zero_proportion_target :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_selberg

/-- Public eventually-logarithmic lower-bound form of the Conrey-style target. -/
theorem conrey_40_percent_zeros_on_critical_line_target_iff_eventually_log_lower_bound :
    KnownResults.conrey_40_percent_zeros_on_critical_line_target ↔
      ∃ c > 0, ∀ᶠ T in atTop,
        (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
          c * (T / (2 * Real.pi) * Real.log T) :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target_iff_eventually_log_lower_bound

/-- Public constructor for the Conrey-style target from the eventually-log
lower-bound form. -/
theorem conrey_40_percent_zeros_on_critical_line_target_of_eventually_log_lower_bound
    (h : ∃ c > 0, ∀ᶠ T in atTop,
      (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
        c * (T / (2 * Real.pi) * Real.log T)) :
    KnownResults.conrey_40_percent_zeros_on_critical_line_target :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target_of_eventually_log_lower_bound h

/-- Public destructor from the Conrey-style target to its eventually-log
lower-bound form. -/
theorem eventually_log_lower_bound_of_conrey_40_percent_zeros_on_critical_line_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ c > 0, ∀ᶠ T in atTop,
      (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥
        c * (T / (2 * Real.pi) * Real.log T) :=
  KnownResults.eventually_log_lower_bound_of_conrey_40_percent_zeros_on_critical_line_target h

/-- Public bridge from Selberg's positive-proportion target to the
Conrey-style 40-percent target statement used in this project. -/
theorem conrey_40_percent_zeros_on_critical_line_target_of_selberg
    (h : HardyTheorem.selberg_zero_proportion_target) :
    KnownResults.conrey_40_percent_zeros_on_critical_line_target :=
  KnownResults.conrey_40_percent_zeros_on_critical_line_target_of_selberg h

/-- Public bridge from the Conrey-style target to Selberg's positive-proportion
target. -/
theorem selberg_zero_proportion_target_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.selberg_zero_proportion_target :=
  KnownResults.selberg_zero_proportion_target_of_conrey_target h

/-- Public bridge from the Conrey-style target to the Hardy-Littlewood linear
lower-bound target. -/
theorem hardy_littlewood_lower_bound_target_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_littlewood_lower_bound_target :=
  KnownResults.hardy_littlewood_lower_bound_target_of_conrey_target h

/-- Public bounded-strip bridge from the Conrey-style target to Hardy's
one-sided unbounded-height target. -/
theorem hardy_zeros_unbounded_of_conrey_target_of_bounded_strips
    (hstrip : ∀ B : ℝ,
      {t : ℝ | |t| ≤ B ∧ riemannZeta (0.5 + Complex.I * t) = 0}.Finite)
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  KnownResults.hardy_zeros_unbounded_of_conrey_target_of_bounded_strips hstrip h

/-- Public extraction of an interval zero from a positive critical-line zero
count. -/
theorem exists_zero_of_zeroCountOnCriticalLine_pos {T : ℝ}
    (h : 0 < HardyTheorem.zeroCountOnCriticalLine T) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.exists_zero_of_zeroCountOnCriticalLine_pos h

/-- Public extraction of an interval Hardy-Z zero from a positive critical-line
zero count. -/
theorem exists_hardyZ_zero_of_zeroCountOnCriticalLine_pos {T : ℝ}
    (h : 0 < HardyTheorem.zeroCountOnCriticalLine T) :
    ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.exists_hardyZ_zero_of_zeroCountOnCriticalLine_pos h

/-- Public finite-set criterion turning an interval zero into a positive
critical-line zero count. -/
theorem zeroCountOnCriticalLine_pos_of_exists_of_finite {T : ℝ}
    (hfinite :
      {t : Set.Icc (0 : ℝ) T |
        riemannZeta (0.5 + Complex.I * (t : ℝ)) = 0}.Finite)
    (h : ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
      riemannZeta (0.5 + Complex.I * t) = 0) :
    0 < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_pos_of_exists_of_finite hfinite h

/-- Public finite-set equivalence between positive zero count and existence of
an interval zero. -/
theorem zeroCountOnCriticalLine_pos_iff_exists_of_finite {T : ℝ}
    (hfinite :
      {t : Set.Icc (0 : ℝ) T |
        riemannZeta (0.5 + Complex.I * (t : ℝ)) = 0}.Finite) :
    0 < HardyTheorem.zeroCountOnCriticalLine T ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
        riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.zeroCountOnCriticalLine_pos_iff_exists_of_finite hfinite

/-- Public finite-set equivalence between positive zero count and existence of
an interval Hardy-Z zero. -/
theorem zeroCountOnCriticalLine_pos_iff_exists_hardyZ_zero_of_finite {T : ℝ}
    (hfinite :
      {t : Set.Icc (0 : ℝ) T |
        riemannZeta (0.5 + Complex.I * (t : ℝ)) = 0}.Finite) :
    0 < HardyTheorem.zeroCountOnCriticalLine T ↔
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  HardyTheorem.zeroCountOnCriticalLine_pos_iff_exists_hardyZ_zero_of_finite hfinite

/-- Public no-zero criterion for a zero critical-line interval count. -/
theorem zeroCountOnCriticalLine_eq_zero_of_no_zero {T : ℝ}
    (h : ¬ ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
      riemannZeta (0.5 + Complex.I * t) = 0) :
    HardyTheorem.zeroCountOnCriticalLine T = 0 :=
  HardyTheorem.zeroCountOnCriticalLine_eq_zero_of_no_zero h

/-- Public finite-set equivalence between zero count and absence of interval
zeros. -/
theorem zeroCountOnCriticalLine_eq_zero_iff_no_zero_of_finite {T : ℝ}
    (hfinite :
      {t : Set.Icc (0 : ℝ) T |
        riemannZeta (0.5 + Complex.I * (t : ℝ)) = 0}.Finite) :
    HardyTheorem.zeroCountOnCriticalLine T = 0 ↔
      ¬ ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧
        riemannZeta (0.5 + Complex.I * t) = 0 :=
  HardyTheorem.zeroCountOnCriticalLine_eq_zero_iff_no_zero_of_finite hfinite

/-- Public monotonicity of the critical-line zero count, under the finite-count
hypothesis at the larger height. -/
theorem zeroCountOnCriticalLine_mono_of_finite {T U : ℝ}
    (hTU : T ≤ U)
    (hfiniteU :
      {t : Set.Icc (0 : ℝ) U |
        riemannZeta (0.5 + Complex.I * (t : ℝ)) = 0}.Finite) :
    HardyTheorem.zeroCountOnCriticalLine T ≤
      HardyTheorem.zeroCountOnCriticalLine U :=
  HardyTheorem.zeroCountOnCriticalLine_mono_of_finite hTU hfiniteU

/-- Public comparison of the interval count to the total critical-line zero
count when the total set is finite. -/
theorem zeroCountOnCriticalLine_le_ncard_allZeros_of_finite
    (T : ℝ)
    (hfinite : {t : ℝ | riemannZeta (0.5 + Complex.I * t) = 0}.Finite) :
    HardyTheorem.zeroCountOnCriticalLine T ≤
      {t : ℝ | riemannZeta (0.5 + Complex.I * t) = 0}.ncard :=
  HardyTheorem.zeroCountOnCriticalLine_le_ncard_allZeros_of_finite T hfinite

/-- Public positivity criterion from a linear lower bound on the interval zero
count. -/
theorem zeroCountOnCriticalLine_pos_of_linear_lower_bound {C T : ℝ}
    (hC : 0 < C) (hT : 0 < T)
    (hbound : C * T ≤ (HardyTheorem.zeroCountOnCriticalLine T : ℝ)) :
    0 < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_pos_of_linear_lower_bound hC hT hbound

/-- Public eventual linear lower bound on critical-line zeros from the
Conrey-style target. -/
theorem eventually_linear_lower_bound_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ C > 0, ∀ᶠ T in atTop,
      (HardyTheorem.zeroCountOnCriticalLine T : ℝ) ≥ C * T :=
  KnownResults.eventually_linear_lower_bound_of_conrey_target h

/-- Public eventual domination of any fixed natural count from the Conrey-style
target. -/
theorem eventually_nat_lt_zeroCountOnCriticalLine_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) (N : ℕ) :
    ∀ᶠ T in atTop, N < HardyTheorem.zeroCountOnCriticalLine T :=
  KnownResults.eventually_nat_lt_zeroCountOnCriticalLine_of_conrey_target h N

/-- Public bridge from eventual domination of every fixed natural count to
unbounded critical-line zero counts. -/
theorem zeroCountOnCriticalLine_unbounded_of_eventually_nat_lt
    (h : ∀ N : ℕ, ∀ᶠ T in atTop,
      N < HardyTheorem.zeroCountOnCriticalLine T) :
    ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_unbounded_of_eventually_nat_lt_zeroCountOnCriticalLine
    h

/-- Public exact-name bridge from eventual domination of every fixed natural
count to unbounded critical-line zero counts. -/
theorem zeroCountOnCriticalLine_unbounded_of_eventually_nat_lt_zeroCountOnCriticalLine
    (h : ∀ N : ℕ, ∀ᶠ T in atTop,
      N < HardyTheorem.zeroCountOnCriticalLine T) :
    ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_unbounded_of_eventually_nat_lt_zeroCountOnCriticalLine
    h

/-- Public zero-count unboundedness from the Hardy--Littlewood linear
lower-bound target. -/
theorem zeroCountOnCriticalLine_unbounded_of_hardy_littlewood_lower_bound
    (h : HardyTheorem.hardy_littlewood_lower_bound_target) :
    ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_unbounded_of_hardy_littlewood_lower_bound h

/-- Public zero-count unboundedness from Selberg's positive-proportion target. -/
theorem zeroCountOnCriticalLine_unbounded_of_selberg_zero_proportion
    (h : HardyTheorem.selberg_zero_proportion_target) :
    ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T :=
  HardyTheorem.zeroCountOnCriticalLine_unbounded_of_selberg_zero_proportion h

/-- Public zero-count unboundedness from the Conrey-style positive-proportion
target. -/
theorem zeroCountOnCriticalLine_unbounded_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T :=
  KnownResults.zeroCountOnCriticalLine_unbounded_of_conrey_target h

/-- Public bridge from unbounded critical-line zero counts to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_zeroCountOnCriticalLine_unbounded
    (h : ∀ N : ℕ, ∃ T : ℝ, N < HardyTheorem.zeroCountOnCriticalLine T) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_zeroCountOnCriticalLine_unbounded h

/-- Public bridge from eventual domination of every fixed natural count to
Hardy's infinite-zero target. -/
theorem hardy_theorem_target_of_eventually_nat_lt_zeroCountOnCriticalLine
    (h : ∀ N : ℕ, ∀ᶠ T in atTop,
      N < HardyTheorem.zeroCountOnCriticalLine T) :
    HardyTheorem.hardy_theorem_target :=
  HardyTheorem.hardy_theorem_target_of_eventually_nat_lt_zeroCountOnCriticalLine h

/-- Public consequence: eventual domination of every fixed natural count gives
infinitely many complex zeros on the critical line. -/
theorem infinitely_many_zeros_on_critical_line_of_eventually_nat_lt_zeroCountOnCriticalLine
    (h : ∀ N : ℕ, ∀ᶠ T in atTop,
      N < HardyTheorem.zeroCountOnCriticalLine T) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_eventually_nat_lt_zeroCountOnCriticalLine
    h

/-- Public eventual positivity of the critical-line zero count from the
Conrey-style target. -/
theorem eventually_zeroCountOnCriticalLine_pos_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∀ᶠ T in atTop, 0 < HardyTheorem.zeroCountOnCriticalLine T :=
  KnownResults.eventually_zeroCountOnCriticalLine_pos_of_conrey_target h

/-- Public bridge from Conrey's positive-proportion target to Hardy's
infinite-zero target. -/
theorem hardy_theorem_target_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_theorem_target :=
  PrimeNumberTheorem.hardy_theorem_target_of_conrey_40_percent_target h

/-- Public bridge from Conrey's positive-proportion target to arbitrarily
large absolute-height critical-line zeros. -/
theorem hardy_zeros_abs_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_abs_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_abs_unbounded_of_conrey_40_percent_target h

/-- Public bridge from Conrey's positive-proportion target to arbitrarily
large positive-height critical-line zeros. -/
theorem hardy_zeros_unbounded_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    HardyTheorem.hardy_zeros_unbounded_target :=
  PrimeNumberTheorem.hardy_zeros_unbounded_of_conrey_40_percent_target h

/-- Public interval-zero consequence of the Conrey-style target. -/
theorem eventually_exists_zero_on_critical_line_interval_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.eventually_exists_zero_on_critical_line_interval_of_conrey_target h

/-- Public Hardy-Z interval-zero consequence of the Conrey-style target. -/
theorem eventually_exists_hardyZ_zero_interval_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∀ᶠ T in atTop,
      ∃ t : ℝ, 0 ≤ t ∧ t ≤ T ∧ HardyTheorem.hardyZ t = 0 :=
  KnownResults.eventually_exists_hardyZ_zero_interval_of_conrey_target h

/-- Public consequence: the Conrey-style target implies infinitely many
critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  KnownResults.infinitely_many_zeros_on_critical_line_of_conrey_target h

/-- Public exact-name bridge from the Conrey-style target to infinitely many
complex critical-line zeros. -/
theorem infinitely_many_zeros_on_critical_line_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    {s : ℂ | s.re = 1 / 2 ∧ riemannZeta s = 0}.Infinite :=
  PrimeNumberTheorem.infinitely_many_zeros_on_critical_line_of_conrey_40_percent_target h

/-- Public consequence: the Conrey-style target implies infinitely many
nontrivial zeros on the critical line. -/
theorem infinitely_many_nontrivial_zeros_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    {s : ℂ | _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine}.Infinite :=
  KnownResults.infinitely_many_nontrivial_zeros_on_critical_line_of_conrey_target h

/-- Public consequence: the Conrey-style target gives at least one real
critical-line zero. -/
theorem exists_zero_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_zero_on_critical_line_of_conrey_target h

/-- Public exact-name bridge from the Conrey-style target to at least one real
critical-line zero. -/
theorem exists_zero_on_critical_line_of_conrey_40_percent_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ t : ℝ, riemannZeta (0.5 + Complex.I * t) = 0 :=
  PrimeNumberTheorem.exists_zero_on_critical_line_of_conrey_40_percent_target h

/-- Public consequence: the Conrey-style target gives at least one nonnegative
real critical-line zero. -/
theorem exists_nonnegative_zero_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ t : ℝ, 0 ≤ t ∧ riemannZeta (0.5 + Complex.I * t) = 0 :=
  KnownResults.exists_nonnegative_zero_on_critical_line_of_conrey_target h

/-- Public consequence: the Conrey-style target gives at least one complex zero
on the critical line. -/
theorem exists_complex_zero_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ s : ℂ, s.re = 1 / 2 ∧ riemannZeta s = 0 :=
  KnownResults.exists_complex_zero_on_critical_line_of_conrey_target h

/-- Public consequence: the Conrey-style target gives at least one nontrivial
zero on the critical line. -/
theorem exists_nontrivial_zero_on_critical_line_of_conrey_target
    (h : KnownResults.conrey_40_percent_zeros_on_critical_line_target) :
    ∃ s : ℂ, _root_.RiemannHypothesis.IsNontrivialZero s ∧
      s ∈ _root_.RiemannHypothesis.criticalLine :=
  KnownResults.exists_nontrivial_zero_on_critical_line_of_conrey_target h

/-- Public definitional unfolding of the corrected height-truncated von
Mangoldt explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ => PrimeNumberTheorem.explicitFormulaApprox x T)
        atTop (𝓝 (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff

/-- Public constructor for the corrected explicit-formula target from an
eventually equal approximation family. -/
theorem explicit_formula_von_mangoldt_of_eventually_eq
    {x : ℝ} {hx : x ≥ 2} {F : ℝ → ℂ}
    (hF : F =ᶠ[atTop]
      fun T : ℝ => PrimeNumberTheorem.explicitFormulaApprox x T)
    (h : Tendsto F atTop (𝓝 (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_eq hF h

/-- Public constructor for the corrected explicit-formula target from eventual
exact equality to `ψ₀`. -/
theorem explicit_formula_von_mangoldt_of_eventually_exact
    {x : ℝ} {hx : x ≥ 2}
    (h : ∀ᶠ T in atTop,
      PrimeNumberTheorem.explicitFormulaApprox x T =
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_exact h

/-- Public constructor for the corrected explicit-formula target from complex
error convergence to zero. -/
theorem explicit_formula_von_mangoldt_of_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto
      (fun T : ℝ =>
        PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
      atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_error_tendsto_zero h

/-- Public elimination from the corrected explicit-formula target to complex
error convergence to zero. -/
theorem explicit_formula_von_mangoldt_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ =>
        PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_error_tendsto_zero h

/-- Public constructor for the corrected explicit-formula target from norm
error convergence to zero. -/
theorem explicit_formula_von_mangoldt_of_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
      atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_norm_error_tendsto_zero h

/-- Public constructor for the corrected explicit-formula target from an
eventual reverse-norm error bound by a function tending to zero. -/
theorem explicit_formula_von_mangoldt_of_eventually_reverse_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
        PrimeNumberTheorem.explicitFormulaApprox x T‖ ≤ E T) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_reverse_norm_le
    hE hbound

/-- Public entry point for the norm-error formulation of the corrected
height-truncated von Mangoldt explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_norm_error_tendsto_zero

/-- Public reverse-norm error formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_reverse_norm_error_tendsto_zero

/-- Public complex error formulation of the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_tendsto_zero

/-- Public reverse complex error formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_reverse_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto (fun T : ℝ =>
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T) atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_reverse_error_tendsto_zero

/-- Public norm-small-o formulation of the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_norm_error_isLittleO_one

/-- Public complex-small-o formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_error_isLittleO_one

/-- Public reverse-complex-small-o formulation of the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_reverse_error_isLittleO_one

/-- Public coordinate convergence formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).re)
        atTop (𝓝 (PrimeNumberTheorem.chebyshevPsi0 x)) ∧
      Tendsto
        (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
        atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_tendsto

/-- Public real/imaginary error formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ =>
          (PrimeNumberTheorem.explicitFormulaApprox x T).re -
            PrimeNumberTheorem.chebyshevPsi0 x)
        atTop (𝓝 0) ∧
      Tendsto
        (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
        atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_error_tendsto_zero

/-- Public coordinate-small-o formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        (PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) ∧
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_error_isLittleO_one

/-- Public absolute real/imaginary error formulation of the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      Tendsto
        (fun T : ℝ =>
          |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
            PrimeNumberTheorem.chebyshevPsi0 x|)
        atTop (𝓝 0) ∧
      Tendsto
        (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
        atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_abs_error_tendsto_zero

/-- Public elimination from the corrected explicit-formula target to real-part
convergence. -/
theorem explicit_formula_von_mangoldt_re_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).re)
      atTop (𝓝 (PrimeNumberTheorem.chebyshevPsi0 x)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_re_tendsto h

/-- Public elimination from the corrected explicit-formula target to
imaginary-part convergence to zero. -/
theorem explicit_formula_von_mangoldt_im_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_im_tendsto_zero h

/-- Public elimination to real-part error convergence. -/
theorem explicit_formula_von_mangoldt_re_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ =>
        (PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_re_error_tendsto_zero h

/-- Public elimination to imaginary-part error convergence. -/
theorem explicit_formula_von_mangoldt_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_im_error_tendsto_zero h

/-- Public constructor from separate real and imaginary convergence. -/
theorem explicit_formula_von_mangoldt_of_re_im_tendsto
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).re)
      atTop (𝓝 (PrimeNumberTheorem.chebyshevPsi0 x)))
    (him : Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
      atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_re_im_tendsto
    hre him

/-- Public constructor from separate real and imaginary error convergence. -/
theorem explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (hre : Tendsto
      (fun T : ℝ =>
        (PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x)
      atTop (𝓝 0))
    (him : Tendsto
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
      atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_re_im_error_tendsto_zero
    hre him

/-- Public elimination to norm-error convergence. -/
theorem explicit_formula_von_mangoldt_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_norm_error_tendsto_zero h

/-- Public elimination to reverse norm-error convergence. -/
theorem explicit_formula_von_mangoldt_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_reverse_norm_error_tendsto_zero h

/-- Public constructor from reverse norm-error convergence. -/
theorem explicit_formula_von_mangoldt_of_reverse_norm_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : Tendsto
      (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖)
      atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_reverse_norm_error_tendsto_zero h

/-- Public elimination to reverse complex-error small-o. -/
theorem explicit_formula_von_mangoldt_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
        PrimeNumberTheorem.explicitFormulaApprox x T)
      =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_reverse_error_isLittleO_one h

/-- Public constructor from reverse complex-error small-o. -/
theorem explicit_formula_von_mangoldt_of_reverse_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h :
      (fun T : ℝ =>
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T)
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_reverse_error_isLittleO_one h

/-- Public elimination to complex-error small-o. -/
theorem explicit_formula_von_mangoldt_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
      =o[atTop] (fun _T : ℝ => (1 : ℂ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_error_isLittleO_one h

/-- Public constructor from complex-error small-o. -/
theorem explicit_formula_von_mangoldt_of_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h :
      (fun T : ℝ =>
        PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
        =o[atTop] (fun _T : ℝ => (1 : ℂ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_error_isLittleO_one h

/-- Public elimination to real-part error small-o. -/
theorem explicit_formula_von_mangoldt_re_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      (PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_re_error_isLittleO_one h

/-- Public elimination to imaginary-part error small-o. -/
theorem explicit_formula_von_mangoldt_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_im_error_isLittleO_one h

/-- Public constructor from real/imaginary error small-o. -/
theorem explicit_formula_von_mangoldt_of_re_im_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (hre :
      (fun T : ℝ =>
        (PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)))
    (him :
      (fun T : ℝ => (PrimeNumberTheorem.explicitFormulaApprox x T).im)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_re_im_error_isLittleO_one
    hre him

/-- Public elimination to absolute real-part error convergence. -/
theorem explicit_formula_von_mangoldt_re_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ =>
        |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x|)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_re_abs_error_tendsto_zero h

/-- Public elimination to absolute imaginary-part error convergence. -/
theorem explicit_formula_von_mangoldt_im_abs_error_tendsto_zero
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    Tendsto
      (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
      atTop (𝓝 0) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_im_abs_error_tendsto_zero h

/-- Public elimination to absolute real-part error small-o. -/
theorem explicit_formula_von_mangoldt_re_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x|)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_re_abs_error_isLittleO_one h

/-- Public elimination to absolute imaginary-part error small-o. -/
theorem explicit_formula_von_mangoldt_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_im_abs_error_isLittleO_one h

/-- Public constructor from absolute real/imaginary error small-o. -/
theorem explicit_formula_von_mangoldt_of_re_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (hre :
      (fun T : ℝ =>
        |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)))
    (him :
      (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_re_im_abs_error_isLittleO_one
    hre him

/-- Public elimination to norm-error small-o. -/
theorem explicit_formula_von_mangoldt_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_norm_error_isLittleO_one h

/-- Public constructor from norm-error small-o. -/
theorem explicit_formula_von_mangoldt_of_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h :
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_norm_error_isLittleO_one h

/-- Public elimination to reverse norm-error small-o. -/
theorem explicit_formula_von_mangoldt_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    (fun T : ℝ =>
      ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
        PrimeNumberTheorem.explicitFormulaApprox x T‖)
      =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_reverse_norm_error_isLittleO_one h

/-- Public constructor from reverse norm-error small-o. -/
theorem explicit_formula_von_mangoldt_of_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2}
    (h :
      (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ))) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_reverse_norm_error_isLittleO_one
    h

/-- Public reverse-norm-small-o formulation of the corrected explicit-formula
target. -/
theorem explicit_formula_von_mangoldt_iff_reverse_norm_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_reverse_norm_error_isLittleO_one

/-- Public absolute-coordinate-small-o formulation of the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_iff_re_im_abs_error_isLittleO_one
    {x : ℝ} {hx : x ≥ 2} :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      (fun T : ℝ =>
        |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) ∧
      (fun T : ℝ => |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
        =o[atTop] (fun _T : ℝ => (1 : ℝ)) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_re_im_abs_error_isLittleO_one

/-- Public exact bridge: if all nontrivial zeros are bounded in height and one
stable truncation equals `ψ₀`, the corrected explicit formula target closes. -/
theorem explicit_formula_von_mangoldt_of_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B)
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_global_height_bound_exact
    hbound hB

/-- Public exact bridge: under a global zero-height bound, the corrected
explicit formula target is equivalent to equality at the stable truncation. -/
theorem explicit_formula_von_mangoldt_iff_global_height_bound_exact
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx ↔
      PrimeNumberTheorem.explicitFormulaApprox x B =
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_iff_global_height_bound_exact
    hbound

/-- Public reverse exact bridge: if the corrected explicit formula target holds
and all nontrivial zeros are globally height-bounded, the stable truncation
equals `ψ₀`. -/
theorem explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound
    {x B : ℝ} {hx : x ≥ 2}
    (hbound : ∀ ρ : ℂ, _root_.RiemannHypothesis.IsNontrivialZero ρ →
      |ρ.im| ≤ B)
    (h : PrimeNumberTheorem.explicit_formula_von_mangoldt x hx) :
    PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ) :=
  PrimeNumberTheorem.explicitFormulaApprox_eq_chebyshevPsi0_of_global_height_bound
    hbound h

/-- Public bridge: any eventual norm error bound by a function tending to zero
closes the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_norm_le
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hbound : ∀ᶠ T in atTop,
      ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖ ≤ E T) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_norm_le
    hE hbound

/-- Public bridge: a Big-O norm error estimate against any function tending to
zero closes the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_norm_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ =>
        ‖PrimeNumberTheorem.explicitFormulaApprox x T -
          (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖)
        =O[atTop] E) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_norm_error_isBigO_tendsto_zero
    hE hO

/-- Public bridge: a reverse-norm Big-O error estimate against any function
tending to zero closes the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_reverse_norm_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {E : ℝ → ℝ}
    (hE : Tendsto E atTop (𝓝 0))
    (hO :
      (fun T : ℝ =>
        ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
          PrimeNumberTheorem.explicitFormulaApprox x T‖)
        =O[atTop] E) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_reverse_norm_error_isBigO_tendsto_zero
    hE hO

/-- Public bridge: an eventual `C/T` norm error estimate closes the corrected
explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)‖ ≤ C * T⁻¹) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_norm_le_const_mul_inv
    hbound

/-- Public bridge: an eventual reverse `C/T` norm error estimate closes the
corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_reverse_norm_le_const_mul_inv
    {x C : ℝ} {hx : x ≥ 2}
    (hbound : ∀ᶠ T in atTop,
      ‖(PrimeNumberTheorem.chebyshevPsi0 x : ℂ) -
        PrimeNumberTheorem.explicitFormulaApprox x T‖ ≤ C * T⁻¹) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_reverse_norm_le_const_mul_inv
    hbound

/-- Public bridge: eventual real and imaginary error bounds by functions
tending to zero close the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_re_im_abs_le
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hre_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x| ≤ Ere T)
    (him_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).im| ≤ Eim T) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_re_im_abs_le
    hEre hEim hre_bound him_bound

/-- Public bridge: Big-O real and imaginary error estimates against functions
tending to zero close the corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_re_im_abs_error_isBigO_tendsto_zero
    {x : ℝ} {hx : x ≥ 2} {Ere Eim : ℝ → ℝ}
    (hEre : Tendsto Ere atTop (𝓝 0))
    (hEim : Tendsto Eim atTop (𝓝 0))
    (hreO :
      (fun T : ℝ =>
        |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
          PrimeNumberTheorem.chebyshevPsi0 x|)
        =O[atTop] Ere)
    (himO :
      (fun T : ℝ =>
        |(PrimeNumberTheorem.explicitFormulaApprox x T).im|)
        =O[atTop] Eim) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_re_im_abs_error_isBigO_tendsto_zero
    hEre hEim hreO himO

/-- Public bridge: eventual `C/T` real and imaginary error estimates close the
corrected explicit-formula target. -/
theorem explicit_formula_von_mangoldt_of_eventually_re_im_abs_le_const_mul_inv
    {x Cre Cim : ℝ} {hx : x ≥ 2}
    (hre_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).re -
        PrimeNumberTheorem.chebyshevPsi0 x| ≤ Cre * T⁻¹)
    (him_bound : ∀ᶠ T in atTop,
      |(PrimeNumberTheorem.explicitFormulaApprox x T).im| ≤ Cim * T⁻¹) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_re_im_abs_le_const_mul_inv
    hre_bound him_bound

/-- Public norm identity for a single nontrivial-zero contribution. -/
theorem norm_zero_contribution_eq
    (ρ : ℂ) {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = x ^ ρ.re / ‖ρ‖ :=
  PrimeNumberTheorem.norm_zero_contribution_eq ρ hx

/-- Public oscillatory formula for a single zero contribution in the explicit
formula. -/
theorem zero_contribution
    (ρ : ℂ) (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ)
    (x : ℝ) (hx : x > 1) :
    (x : ℂ) ^ ρ / ρ =
      Real.exp (ρ.re * Real.log x) *
        (Real.cos (ρ.im * Real.log x) +
          Complex.I * Real.sin (ρ.im * Real.log x)) / ρ :=
  PrimeNumberTheorem.zero_contribution ρ hρ x hx

/-- Public RH specialization: each nontrivial-zero contribution has
`sqrt x` amplitude. -/
theorem norm_zero_contribution_eq_sqrt_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ)
    {x : ℝ} (hx : 0 < x) :
    ‖(x : ℂ) ^ ρ / ρ‖ = Real.sqrt x / ‖ρ‖ :=
  PrimeNumberTheorem.norm_zero_contribution_eq_sqrt_of_RH hRH hρ hx

/-- Public RH bound for any finite sum of nontrivial-zero contributions. -/
theorem norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x : ℝ} (hx : 0 < x) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ‖∑ ρ ∈ S, (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x * ∑ ρ ∈ S, ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_sum_zero_contributions_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx S hS

/-- Public RH bound for the height-truncated nontrivial-zero sum. -/
theorem norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖PrimeNumberTheorem.finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x *
        ∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_finiteNontrivialZeroSum_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx

/-- Public RH bound for the new-zero contribution between two truncation
heights. -/
theorem norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_new_zero_contribution_sum_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx

/-- Public RH lower bound for the norm of a nontrivial zero. -/
theorem norm_nontrivial_zero_ge_half_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    (1 / 2 : ℝ) ≤ ‖ρ‖ :=
  PrimeNumberTheorem.norm_nontrivial_zero_ge_half_of_RH hRH hρ

/-- Public RH upper bound for the reciprocal norm of a nontrivial zero. -/
theorem inv_norm_nontrivial_zero_le_two_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {ρ : ℂ} (hρ : _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    ‖ρ‖⁻¹ ≤ (2 : ℝ) :=
  PrimeNumberTheorem.inv_norm_nontrivial_zero_le_two_of_RH hRH hρ

/-- Public RH bound for finite reciprocal-norm zero sums. -/
theorem sum_inv_norm_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, _root_.RiemannHypothesis.IsNontrivialZero ρ) :
    (∑ ρ ∈ S, ‖ρ‖⁻¹) ≤ (2 : ℝ) * S.card :=
  PrimeNumberTheorem.sum_inv_norm_le_two_card_of_RH hRH S hS

/-- Public RH bound for the truncated reciprocal-norm zero sum. -/
theorem sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (T : ℝ) :
    (∑ ρ ∈ PrimeNumberTheorem.nontrivialZerosFinset T, ‖ρ‖⁻¹) ≤
      (2 : ℝ) * (PrimeNumberTheorem.nontrivialZerosFinset T).card :=
  PrimeNumberTheorem.sum_inv_norm_nontrivialZerosFinset_le_two_card_of_RH
    hRH T

/-- Public RH bound for reciprocal-norm sums over newly appearing zeros. -/
theorem sum_inv_norm_new_zeros_le_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement) (T U : ℝ) :
    (∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹) ≤
      (2 : ℝ) *
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T).card :=
  PrimeNumberTheorem.sum_inv_norm_new_zeros_le_two_card_of_RH hRH T U

/-- Public RH count-bound for the height-truncated nontrivial-zero sum. -/
theorem norm_finiteNontrivialZeroSum_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T : ℝ} (hx : 0 < x) :
    ‖PrimeNumberTheorem.finiteNontrivialZeroSum x T‖ ≤
      Real.sqrt x *
        ((2 : ℝ) * (PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_finiteNontrivialZeroSum_le_sqrt_mul_two_card_of_RH
    hRH hx

/-- Public RH count-bound for the new-zero contribution between truncation
heights. -/
theorem norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) :
    ‖∑ ρ ∈
        (PrimeNumberTheorem.nontrivialZerosFinset U \
          PrimeNumberTheorem.nontrivialZerosFinset T),
        (x : ℂ) ^ ρ / ρ‖ ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_new_zero_contribution_sum_le_sqrt_mul_two_card_of_RH
    hRH hx

/-- Public RH Cauchy-type bound for two explicit-formula truncations,
measured by the reciprocal-norm sum of newly included zeros. -/
theorem norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.norm_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public RH Cauchy-type bound for two explicit-formula truncations,
measured by the number of newly included zeros. -/
theorem norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    ‖PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U‖ ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.norm_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public real-part RH Cauchy-type truncation bound, measured by the
reciprocal-norm sum of newly included zeros. -/
theorem abs_re_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.abs_re_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public imaginary-part RH Cauchy-type truncation bound, measured by the
reciprocal-norm sum of newly included zeros. -/
theorem abs_im_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ∑ ρ ∈
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T), ‖ρ‖⁻¹ :=
  PrimeNumberTheorem.abs_im_explicitFormulaApprox_sub_le_sqrt_mul_sum_inv_norm_of_RH
    hRH hx hTU

/-- Public real-part RH Cauchy-type truncation bound, measured by the number of
newly included zeros. -/
theorem abs_re_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).re| ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.abs_re_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public imaginary-part RH Cauchy-type truncation bound, measured by the
number of newly included zeros. -/
theorem abs_im_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    (hRH : _root_.RiemannHypothesis.Statement)
    {x T U : ℝ} (hx : 0 < x) (hTU : T ≤ U) :
    |(PrimeNumberTheorem.explicitFormulaApprox x T -
        PrimeNumberTheorem.explicitFormulaApprox x U).im| ≤
      Real.sqrt x *
        ((2 : ℝ) *
          (PrimeNumberTheorem.nontrivialZerosFinset U \
            PrimeNumberTheorem.nontrivialZerosFinset T).card) :=
  PrimeNumberTheorem.abs_im_explicitFormulaApprox_sub_le_sqrt_mul_two_card_of_RH
    hRH hx hTU

/-- Public conditional explicit-formula bridge from an RH reciprocal-norm tail
bound over newly included zeros. -/
theorem explicit_formula_von_mangoldt_of_RH_base_and_new_zero_sum_tendsto_zero
    (hRH : _root_.RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ∑ ρ ∈
              (PrimeNumberTheorem.nontrivialZerosFinset T \
                PrimeNumberTheorem.nontrivialZerosFinset B), ‖ρ‖⁻¹)
        atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_RH_base_and_new_zero_sum_tendsto_zero
    hRH hB htail

/-- Public conditional explicit-formula bridge from an RH zero-count tail bound
over newly included zeros. -/
theorem explicit_formula_von_mangoldt_of_RH_base_and_new_zero_card_tendsto_zero
    (hRH : _root_.RiemannHypothesis.Statement)
    {x B : ℝ} {hx : x ≥ 2}
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ))
    (htail :
      Tendsto
        (fun T : ℝ =>
          Real.sqrt x *
            ((2 : ℝ) *
              (PrimeNumberTheorem.nontrivialZerosFinset T \
                PrimeNumberTheorem.nontrivialZerosFinset B).card))
        atTop (𝓝 0)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_RH_base_and_new_zero_card_tendsto_zero
    hRH hB htail

/-- Public stability bridge: if the zero sum has no new terms eventually and
the stable truncation equals `ψ₀(x)`, then the explicit-formula target follows. -/
theorem explicit_formula_von_mangoldt_of_eventually_no_new_zeros
    {x B : ℝ} {hx : x ≥ 2}
    (hnew : ∀ᶠ T in atTop,
      B ≤ T ∧
        PrimeNumberTheorem.nontrivialZerosFinset T \
            PrimeNumberTheorem.nontrivialZerosFinset B = ∅)
    (hB : PrimeNumberTheorem.explicitFormulaApprox x B =
      (PrimeNumberTheorem.chebyshevPsi0 x : ℂ)) :
    PrimeNumberTheorem.explicit_formula_von_mangoldt x hx :=
  PrimeNumberTheorem.explicit_formula_von_mangoldt_of_eventually_no_new_zeros
    hnew hB

/-- Public Gamma-asymptotic target in its unfolded asymptotic form. -/
theorem gamma_asymptotic_half_plus_it_target_iff_asymptotic :
    HardyTheorem.Details.gamma_asymptotic_half_plus_it_target ↔
      (fun (t : ℝ) => Complex.Gamma (0.5 + Complex.I * t)) ~[atTop]
        (fun (t : ℝ) => Real.sqrt (2*Real.pi) *
          Complex.exp (Complex.I * t * Real.log t - Complex.I * t) *
          Complex.exp (-Real.pi * t / 2)) :=
  HardyTheorem.Details.gamma_asymptotic_half_plus_it_target_iff_asymptotic

/-- Public constructor for the Gamma-asymptotic target. -/
theorem gamma_asymptotic_half_plus_it_target_of_asymptotic
    (h :
      (fun (t : ℝ) => Complex.Gamma (0.5 + Complex.I * t)) ~[atTop]
        (fun (t : ℝ) => Real.sqrt (2*Real.pi) *
          Complex.exp (Complex.I * t * Real.log t - Complex.I * t) *
          Complex.exp (-Real.pi * t / 2))) :
    HardyTheorem.Details.gamma_asymptotic_half_plus_it_target :=
  HardyTheorem.Details.gamma_asymptotic_half_plus_it_target_of_asymptotic h

/-- Public unfolded form of the unwrapped theta-asymptotic target. -/
theorem theta_asymptotic_target_iff_exists :
    HardyTheorem.Details.theta_asymptotic_target ↔
      ∃ theta : ℝ → ℝ,
        (∀ t : ℝ, Complex.exp (Complex.I * theta t) =
          Complex.exp (Complex.I * HardyTheorem.thetaPhase t)) ∧
        (fun t : ℝ => theta t) ~[atTop]
          (fun t : ℝ =>
            (t/2) * Real.log (t/(2*Real.pi)) - t/2 - Real.pi/8) :=
  HardyTheorem.Details.theta_asymptotic_target_iff_exists

/-- Public constructor for the unwrapped theta-asymptotic target. -/
theorem theta_asymptotic_target_of
    (theta : ℝ → ℝ)
    (hphase : ∀ t : ℝ, Complex.exp (Complex.I * theta t) =
      Complex.exp (Complex.I * HardyTheorem.thetaPhase t))
    (hasymp :
      (fun t : ℝ => theta t) ~[atTop]
        (fun t : ℝ =>
          (t/2) * Real.log (t/(2*Real.pi)) - t/2 - Real.pi/8)) :
    HardyTheorem.Details.theta_asymptotic_target :=
  HardyTheorem.Details.theta_asymptotic_target_of theta hphase hasymp

/-- Public direct constructor for the approximate-functional-equation target
from a global remainder estimate. -/
theorem approximate_functional_equation_target_of
    (C : ℝ) (hC : 0 < C)
    (hrem : ∀ t : ℝ, t > 1 → ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ C * (t : ℝ)^(-1/4 : ℝ)) :
    HardyTheorem.Details.approximate_functional_equation_target :=
  HardyTheorem.Details.approximate_functional_equation_target_of C hC hrem

/-- Public destructor: the approximate-functional-equation target supplies an
eventual large-height remainder estimate. -/
theorem eventually_approximate_functional_equation_of_target
    (h : HardyTheorem.Details.approximate_functional_equation_target) :
    ∃ C : ℝ, C > 0 ∧ Filter.Eventually (fun t : ℝ => ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ C * (t : ℝ)^(-1/4 : ℝ)) atTop :=
  HardyTheorem.Details.eventually_approximate_functional_equation_of_target h

/-- Public patching bridge for the approximate functional equation target:
large-height analytic estimates plus bounded-height estimates close the global
target. -/
theorem approximate_functional_equation_target_of_threshold_bounds
    (Clarge Csmall T : ℝ) (hC : 0 < max Clarge Csmall)
    (hlarge : ∀ t : ℝ, T ≤ t → ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ Clarge * (t : ℝ)^(-1/4 : ℝ))
    (hsmall : ∀ t : ℝ, 1 < t → t < T → ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ Csmall * (t : ℝ)^(-1/4 : ℝ)) :
    HardyTheorem.Details.approximate_functional_equation_target :=
  HardyTheorem.Details.approximate_functional_equation_target_of_threshold_bounds
    Clarge Csmall T hC hlarge hsmall

/-- Public patching bridge for the approximate functional equation target from
an eventually valid large-height estimate plus bounded-height patches. -/
theorem approximate_functional_equation_target_of_eventually_and_bounded_patch
    (Clarge Csmall : ℝ) (hC : 0 < max Clarge Csmall)
    (hlarge : Filter.Eventually (fun t : ℝ => ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ Clarge * (t : ℝ)^(-1/4 : ℝ)) atTop)
    (hsmall : ∀ T t : ℝ, 1 < t → t < T → ∃ R : ℂ,
      (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
        ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
          1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
        + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
          ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
            1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
        + R) ∧ ‖R‖ ≤ Csmall * (t : ℝ)^(-1/4 : ℝ)) :
    HardyTheorem.Details.approximate_functional_equation_target :=
  HardyTheorem.Details.approximate_functional_equation_target_of_eventually_and_bounded_patch
    Clarge Csmall hC hlarge hsmall

/-- Public iff form of the approximate-functional-equation target: an
eventually valid large-height estimate plus bounded-height patches is exactly
the global target statement. -/
theorem approximate_functional_equation_target_iff_eventually_and_bounded_patch :
    HardyTheorem.Details.approximate_functional_equation_target ↔
      ∃ Clarge Csmall : ℝ, 0 < max Clarge Csmall ∧
        Filter.Eventually (fun t : ℝ => ∃ R : ℂ,
          (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
            ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
              1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
            + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
              ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
                1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
            + R) ∧ ‖R‖ ≤ Clarge * (t : ℝ)^(-1/4 : ℝ)) atTop ∧
        ∀ T t : ℝ, 1 < t → t < T → ∃ R : ℂ,
          (riemannZeta (0.5 + Complex.I * (t : ℂ)) =
            ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
              1/((n+1 : ℂ) ^ (0.5 + Complex.I * (t : ℂ)))
            + Complex.exp (Complex.I * (HardyTheorem.thetaPhase t : ℂ)) *
              ∑ n ∈ Finset.range (Nat.floor (Real.sqrt ((t : ℝ) / (2*Real.pi)))),
                1/((n+1 : ℂ) ^ (0.5 - Complex.I * (t : ℂ)))
            + R) ∧ ‖R‖ ≤ Csmall * (t : ℝ)^(-1/4 : ℝ) :=
  HardyTheorem.Details.approximate_functional_equation_target_iff_eventually_and_bounded_patch

end RiemannPNT.API
