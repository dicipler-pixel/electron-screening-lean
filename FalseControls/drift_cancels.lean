import ElectronScreening.Basic
-- An uninterleaved 3%/h drift over six hours does not cancel: it forges ~53 eV, not under 5.
example : (0.03 * 6 : ℝ) / 0.0034 < 5 := by norm_num
