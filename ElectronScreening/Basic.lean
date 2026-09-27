/-
Electron Screening in Metal Deuterides: Measurement Systematics, Evolving Target State, and an
Experimental Arbitration Protocol (Jeromie Beasley, DOI 10.5281/zenodo.21935285): the exact
statements and the arithmetic behind the paper's numbers.

* Sec. 6.2, the direction of the fitting bias: if the rate `R` is increasing and convex in `U_e`,
  the value `U_fit` returned by averaging in yield space (`R(U_fit) = mean R(U_k)`) is at least
  the campaign mean and at most the largest value traversed (Jensen).
* Eq. (1): `d/dU [−√(E_G/(E+U))] = ½ √E_G (E+U)^{−3/2}`, the sensitivity of `ln R`.
* Sec. 7.2: the two-energy ratio cancels every energy-independent factor.
* Sec. 3: one watt at 3.65 MeV per reaction is `1.71 × 10¹²` reactions per second and
  `8.6 × 10¹¹` neutrons; at 23.85 MeV it is `2.6 × 10¹¹` pair creations.
* Sec. 5.3: `340 eV / 100 meV = 3400` phonons in phase.
* Sec. 7.3–7.5: the quadrature total `0.024`, `σ_Ue ≈ 7.1 eV`, `≈ 2.9 eV` on the six-step trend,
  the 34σ and 14σ discriminations, and the drift residuals `r τ / s`.
-/
import Mathlib

namespace ElectronScreening

open Real

/-! ## Sec. 6.2: the fitting bias points up -/

/-- **The direction of the bias.** Let `R` be monotone and convex on an interval containing the
screening values `U_k` traversed during acquisition, with positive weights `w_k` summing to one.
If `U_fit` is defined by averaging in yield space, `R(U_fit) = Σ w_k R(U_k)`, and `R` is strictly
monotone, then `U_fit` is at least the weighted mean `Σ w_k U_k`. -/
theorem fit_above_mean {ι : Type*} (s : Finset ι) (w U : ι → ℝ) (R : ℝ → ℝ) (I : Set ℝ)
    (hR : ConvexOn ℝ I R) (hmono : StrictMonoOn R I) (hw : ∀ k ∈ s, 0 ≤ w k)
    (hw1 : ∑ k ∈ s, w k = 1) (hU : ∀ k ∈ s, U k ∈ I) (Ufit : ℝ) (hfit : Ufit ∈ I)
    (hdef : R Ufit = ∑ k ∈ s, w k * R (U k)) : ∑ k ∈ s, w k * U k ≤ Ufit := by
  have hmean : ∑ k ∈ s, w k * U k ∈ I := by
    have := hR.1.sum_mem hw hw1 hU
    simpa [smul_eq_mul] using this
  have hj := hR.map_sum_le hw hw1 hU
  simp only [smul_eq_mul] at hj
  rw [← hdef] at hj
  exact (hmono.le_iff_le hmean hfit).mp hj

/-- **The fit never exceeds the top of the range.** With the same hypotheses and `R` monotone,
`R(U_fit) ≤ R(max U_k)`, so `U_fit ≤ max U_k`. -/
theorem fit_below_max {ι : Type*} (s : Finset ι) (w U : ι → ℝ) (R : ℝ → ℝ) (I : Set ℝ)
    (hmono : StrictMonoOn R I) (hw : ∀ k ∈ s, 0 ≤ w k) (hw1 : ∑ k ∈ s, w k = 1)
    (hU : ∀ k ∈ s, U k ∈ I) (Umax : ℝ) (hmax : Umax ∈ I) (hle : ∀ k ∈ s, U k ≤ Umax)
    (Ufit : ℝ) (hfit : Ufit ∈ I) (hdef : R Ufit = ∑ k ∈ s, w k * R (U k)) : Ufit ≤ Umax := by
  have h : R Ufit ≤ R Umax := by
    rw [hdef]
    calc ∑ k ∈ s, w k * R (U k) ≤ ∑ k ∈ s, w k * R Umax := by
          apply Finset.sum_le_sum
          intro k hk
          exact mul_le_mul_of_nonneg_left
            ((hmono.le_iff_le (hU k hk) hmax).mpr (hle k hk)) (hw k hk)
      _ = R Umax := by rw [← Finset.sum_mul, hw1, one_mul]
  exact (hmono.le_iff_le hfit hmax).mp h

/-! ## Eq. (1): the sensitivity of the rate to `U_e` -/

/-- **Sensitivity.** `d/dU [−√(E_G/(E+U))] = ½ √E_G (E+U)^{−3/2}` for `E + U > 0`. -/
theorem log_rate_deriv (EG E U : ℝ) (hEG : 0 < EG) (hx : 0 < E + U) :
    HasDerivAt (fun u => -√(EG / (E + u))) (1 / 2 * √EG * (E + U) ^ (-(3 / 2 : ℝ))) U := by
  have hx' : (E + U) ≠ 0 := hx.ne'
  have h1 : HasDerivAt (fun u => EG / (E + u)) (-(EG / (E + U) ^ 2)) U := by
    have := ((hasDerivAt_id U).const_add E).inv hx'
    simpa [div_eq_mul_inv, id, pow_two] using this.const_mul EG
  have hpos : 0 < EG / (E + U) := div_pos hEG hx
  have h2 := (h1.sqrt hpos.ne').neg
  convert h2 using 1
  rw [Real.sqrt_div hEG.le, Real.rpow_neg hx.le, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
    Real.rpow_add hx, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hs : 0 < √(E + U) := Real.sqrt_pos.mpr hx
  have hs2 : √(E + U) ^ 2 = E + U := Real.sq_sqrt hx.le
  have hEG2 : √EG ^ 2 = EG := Real.sq_sqrt hEG.le
  field_simp
  try simp only [hEG2, hs2]
  try ring

/-! ## Sec. 7.2: the ratio cancels every energy-independent factor -/

/-- **The two-energy ratio.** Target density, charge integration, secondary-electron correction
and solid angle multiply both yields and cancel: `(c R₁)/(c R₂) = R₁/R₂` for `c ≠ 0`. -/
theorem ratio_cancels (c R1 R2 : ℝ) (hc : c ≠ 0) : (c * R1) / (c * R2) = R1 / R2 :=
  mul_div_mul_left R1 R2 hc

/-! ## The paper's numbers -/

/-- The elementary charge in coulombs (exact SI value). -/
def e : ℚ := 1602176634 / 10 ^ 28

/-- **Sec. 3.** One watt at 3.65 MeV per reaction is between `1.71 × 10¹²` and
`1.72 × 10¹²` reactions per second, and half of those, `8.6 × 10¹¹`, are neutrons. -/
theorem watt_reactions :
    (171 : ℚ) * 10 ^ 10 < 1 / (365 / 100 * 10 ^ 6 * e) ∧ 1 / (365 / 100 * 10 ^ 6 * e) < 172 * 10 ^ 10 ∧
      (85 : ℚ) * 10 ^ 10 < 1 / (365 / 100 * 10 ^ 6 * e) / 2 ∧
        1 / (365 / 100 * 10 ^ 6 * e) / 2 < 86 * 10 ^ 10 := by
  norm_num [e]

/-- **Sec. 8.** One watt through the 23.85 MeV channel is about `2.6 × 10¹¹` pair creations per
second. -/
theorem watt_pairs :
    (26 : ℚ) * 10 ^ 10 < 1 / (2385 / 100 * 10 ^ 6 * e) ∧ 1 / (2385 / 100 * 10 ^ 6 * e) < 27 * 10 ^ 10 := by
  norm_num [e]

/-- **Sec. 5.3.** The 340 eV scale is 3400 phonons of 100 meV in phase at one site. -/
theorem phonons_in_phase : (340 : ℚ) / (100 / 1000) = 3400 := by norm_num

/-- **Sec. 7.3.** The quadrature total of the independent terms is `0.024`:
`0.020² + 0.005² + 0.004² + 0.002² + 0.006² + 0.005² + 0.010² = 0.000606`, and its square root lies
in `(0.0246, 0.0247)`. -/
theorem quadrature_total :
    (0.020 : ℝ) ^ 2 + 0.005 ^ 2 + 0.004 ^ 2 + 0.002 ^ 2 + 0.006 ^ 2 + 0.005 ^ 2 + 0.010 ^ 2 =
        0.000606 ∧ 0.0246 < √(0.000606 : ℝ) ∧ √(0.000606 : ℝ) < 0.0247 := by
  refine ⟨by norm_num, ?_, ?_⟩
  · rw [Real.lt_sqrt (by norm_num)]; norm_num
  · rw [Real.sqrt_lt' (by norm_num)]; norm_num

/-- **Sec. 7.3.** With ratio sensitivity `3.40 × 10⁻³ eV⁻¹`, a 0.024 ratio error is
`σ_Ue ≈ 7.1 eV` per step, and `≈ 2.9 eV` on the trend over six steps. -/
theorem sigma_Ue :
    (70 : ℝ) / 10 < 0.024 / 0.0034 ∧ (0.024 : ℝ) / 0.0034 < 71 / 10 ∧
      2.8 < (0.024 / 0.0034) / √6 ∧ (0.024 / 0.0034) / √6 < 2.9 := by
  have h6 : (2.449 : ℝ) < √6 := by rw [Real.lt_sqrt (by norm_num)]; norm_num
  have h6' : √6 < (2.4495 : ℝ) := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hp : (0 : ℝ) < √6 := by positivity
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩
  · rw [lt_div_iff₀ hp]; nlinarith
  · rw [div_lt_iff₀ hp]; nlinarith

/-- **Sec. 7.5.** At `σ_Ue = 0.024/0.0034` the disputed 100–340 eV span is resolved at more
than 33σ and a 300 → 400 eV drift at more than 14σ. -/
theorem discrimination :
    33 < (340 - 100 : ℝ) / (0.024 / 0.0034) ∧ 14 < (400 - 300 : ℝ) / (0.024 / 0.0034) := by
  norm_num

/-- **Sec. 7.4.** An uninterleaved 3%/h drift over six hours forges `r τ / s ≈ 53 eV`; with
five-minute swaps it is `≈ 0.7 eV`. -/
theorem drift_residuals :
    52 < (0.03 * 6 : ℝ) / 0.0034 ∧ (0.03 * 6 : ℝ) / 0.0034 < 53 ∧
      0.7 < (0.03 * (5 / 60) : ℝ) / 0.0034 ∧ (0.03 * (5 / 60) : ℝ) / 0.0034 < 0.75 := by
  norm_num

end ElectronScreening
