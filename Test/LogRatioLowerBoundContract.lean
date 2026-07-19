import MathlibAux.LogRatioLowerBound

#check MathlibAux.abs_sub_div_max_le_abs_log_div

example {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    |x - y| / max x y ≤ |Real.log (x / y)| :=
  MathlibAux.abs_sub_div_max_le_abs_log_div hx hy

#print axioms MathlibAux.abs_sub_div_max_le_abs_log_div
