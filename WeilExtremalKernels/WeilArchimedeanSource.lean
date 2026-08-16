import WeilExtremalKernels.WeilPrimeSource
import WeilExtremalKernels.ArchimedeanImproperTail

/-!
# The concrete archimedean source data

The paper defines the finite-cutoff archimedean source by integrating the
sine-chord kernel against the completed-zeta density `hPlus`.  This module
records that source and its formal derivative integrand directly.

The remaining analytic theorem is to justify differentiation under the
integrals and identify source increments with the existing rank-two tail
matrix.  No hypergeometric or Lerch function is needed for this definition.
-/

namespace WeilExtremalKernels

open MeasureTheory
open scoped Interval

/-- Sine-chord source kernel before archimedean integration. -/
noncomputable def paperSineChord
    (L r x : Real) : Real :=
  ∫ y in (0 : Real)..L,
    Real.sin (2 * Real.pi * x * (1 - y / L)) *
      Real.cos (r * y)

/-- Formal `x`-derivative integrand of the sine-chord source. -/
noncomputable def paperSineChordDerivative
    (L r x : Real) : Real :=
  ∫ y in (0 : Real)..L,
    2 * Real.pi * (1 - y / L) *
      Real.cos (2 * Real.pi * x * (1 - y / L)) *
      Real.cos (r * y)

/-- Finite-`T` archimedean source value from the Guinand-Weil dictionary. -/
noncomputable def finiteArchimedeanSourceValue
    (L T : Real) (n : Int) : Real :=
  (1 / (2 * Real.pi ^ 2)) *
    ∫ r in (-T)..T,
      archimedeanHPlus r * paperSineChord L r (n : Real)

/-- Candidate derivative data obtained by differentiating the sine-chord
integrand with respect to its real source variable. -/
noncomputable def finiteArchimedeanSourceDerivative
    (L T : Real) (n : Int) : Real :=
  (1 / (2 * Real.pi ^ 2)) *
    ∫ r in (-T)..T,
      archimedeanHPlus r *
        paperSineChordDerivative L r (n : Real)

/-- Concrete finite-`T` archimedean source data. -/
noncomputable def finiteArchimedeanSourceData
    (L T : Real) : WeilSourceData where
  value := finiteArchimedeanSourceValue L T
  derivative := finiteArchimedeanSourceDerivative L T

/-- Finite archimedean source cutoffs are centered sections of one global
integer kernel at each fixed `L,T`. -/
theorem finiteArchimedeanSourceData_centered_nested
    (L T : Real) {M N : Nat} (hMN : M <= N) :
    sourceCutoffMatrix (finiteArchimedeanSourceData L T) M =
      centeredPrincipalSection hMN
        (sourceCutoffMatrix
          (finiteArchimedeanSourceData L T) N) := by
  exact sourceCutoffMatrix_centered_nested
    (finiteArchimedeanSourceData L T) hMN

/-- Difference of source data at two archimedean cutoffs. -/
noncomputable def archimedeanSourceIncrementData
    (L T1 T2 : Real) : WeilSourceData where
  value := fun n =>
    finiteArchimedeanSourceValue L T2 n -
      finiteArchimedeanSourceValue L T1 n
  derivative := fun n =>
    finiteArchimedeanSourceDerivative L T2 n -
      finiteArchimedeanSourceDerivative L T1 n

/-- Loewner kernels commute with subtraction of source data. -/
theorem integerLoewnerKernel_sub
    (value1 value2 derivative1 derivative2 : Int -> Real)
    (m n : Int) :
    integerLoewnerKernel
        (fun k => value1 k - value2 k)
        (fun k => derivative1 k - derivative2 k) m n =
      integerLoewnerKernel value1 derivative1 m n -
        integerLoewnerKernel value2 derivative2 m n := by
  by_cases hmn : m = n
  · subst n
    simp [integerLoewnerKernel]
  · simp [integerLoewnerKernel, hmn]
    ring

/-- The source increment kernel is exactly the difference of the two
finite-cutoff source kernels. -/
theorem archimedeanSourceIncrementData_kernel
    (L T1 T2 : Real) (m n : Int) :
    (archimedeanSourceIncrementData L T1 T2).kernel m n =
      (finiteArchimedeanSourceData L T2).kernel m n -
        (finiteArchimedeanSourceData L T1).kernel m n := by
  exact integerLoewnerKernel_sub
    (finiteArchimedeanSourceValue L T2)
    (finiteArchimedeanSourceValue L T1)
    (finiteArchimedeanSourceDerivative L T2)
    (finiteArchimedeanSourceDerivative L T1) m n

/-- Exact compatibility proposition still required to connect the source
increment to the already formalized rank-two matrix increment. -/
def ArchimedeanSourceIncrementCompatible
    (L rho T1 T2 : Real) (N : Nat) : Prop :=
  sourceCutoffMatrix
      (archimedeanSourceIncrementData L T1 T2) N =
    paperActualArchimedeanRankTwoIncrement N L rho T1 T2

/-- Once source-increment compatibility is proved analytically, the existing
rank-two positivity theorem transfers immediately to the source cutoff
difference. -/
theorem quadraticForm_archimedeanSourceIncrement_nonneg_of_compatible
    (L rho T1 T2 : Real) (N : Nat)
    (hcompatible :
      ArchimedeanSourceIncrementCompatible L rho T1 T2 N)
    (hTail :
      forall x,
        0 <= quadraticForm
          (paperActualArchimedeanRankTwoIncrement
            N L rho T1 T2) x) :
    forall x,
      0 <= quadraticForm
        (sourceCutoffMatrix
          (archimedeanSourceIncrementData L T1 T2) N) x := by
  intro x
  rw [hcompatible]
  exact hTail x

end WeilExtremalKernels
