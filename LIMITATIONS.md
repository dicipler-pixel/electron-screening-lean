# What is not proved here

Lean proves exactly the statements written, under exactly the hypotheses written.

* The bias theorems assume the rate is increasing and convex over the range traversed. For
  `R = exp(−√(E_G/(E+U)))` that holds for `E + U ≤ E_G/9 ≈ 110 keV`, which covers the
  measurement range. That convexity condition is stated but not formalized.
* The magnitude of the bias (28–42%), the identifiability correlations (`ρ ≈ −0.98`) and the
  likelihood-ratio powers are simulation results, not Lean proofs.
* The sensitivities `2.57 × 10⁻³` and `3.40 × 10⁻³ eV⁻¹` are evaluations of the proved
  derivative formula. Their numerical values enter `sigma_Ue`, `discrimination` and
  `drift_residuals` as inputs.
* Sections 4, 5.2, 5.4, 8 (the resonance claim), 9 and 10 are not formalized.
