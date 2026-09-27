import ElectronScreening.Basic
-- The per-step resolution is about 7 eV, not 30 eV.
example : (30 : ℝ) < 0.024 / 0.0034 := by norm_num
