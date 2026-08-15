import PrimeNumberTheorem.PerronTruncation

example : Complex.addCommGroup =
    DenselyNormedField.toNontriviallyNormedField.toDivisionRing.toAddCommGroup := by
  rfl

example : (Semiring.toModule : Module ℂ ℂ) =
    (NormedAlgebra.toNormedSpace ℂ).toModule := by
  rfl
