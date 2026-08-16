import PrimeNumberTheorem.PerronTruncation

example (f g : ℂ → ℂ) (z : ℂ) : (f - g) z = f z - g z := by
  rfl

example (f g : ℂ → ℂ) (z : ℂ) : (f - g) = fun z => f z - g z := by
  funext z
  rfl

example (f g : ℂ → ℂ) (z : ℂ) : AnalyticAt ℂ (f - g) z = AnalyticAt ℂ (fun w => f w - g w) z := by
  rfl
