import ElectronScreening.Basic
-- One watt is ~1.7 × 10¹² reactions per second, not ~10⁶.
example : 1 / (365 / 100 * 10 ^ 6 * ElectronScreening.e) < (10 : ℚ) ^ 6 := by
  norm_num [ElectronScreening.e]
