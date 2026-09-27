<div align="center">

# Electron Screening in Metal Deuterides: Measurement Systematics, Evolving Target State, and an Experimental Arbitration Protocol — Lean proofs

[![Lean proof check](https://github.com/dicipler-pixel/electron-screening-lean/actions/workflows/build.yml/badge.svg)](https://github.com/dicipler-pixel/electron-screening-lean/actions/workflows/build.yml)
![Lean](https://img.shields.io/badge/Lean-v4.34.1-blue)
![Theorems](https://img.shields.io/badge/theorems-11-2EA043)
![sorry](https://img.shields.io/badge/sorry-0-2EA043)
![Code: MIT](https://img.shields.io/badge/code-MIT-lightgrey)
![Text: CC BY 4.0](https://img.shields.io/badge/text-CC%20BY%204.0-lightgrey)
[![Paper DOI](https://img.shields.io/badge/paper-10.5281%2Fzenodo.21935285-blue)](https://doi.org/10.5281/zenodo.21935285)

Jeromie Beasley

</div>

---

## The idea in one line

A screening curve is fitted by averaging in yield space. Because the rate grows exponentially
with `U_e`, an evolving target drags the fitted value upward. The fix is a two-energy ratio,
which cancels every factor that does not depend on energy. This repository proves those
statements, and it checks the arithmetic behind every number the protocol relies on.

## What is proved

| Paper | Result | Theorem |
| :--- | :--- | :--- |
| Sec. 6.2 | For an increasing, convex rate, the yield-space fit `U_fit` is at least the campaign mean (Jensen), and at most the top of the range traversed | `fit_above_mean`, `fit_below_max` |
| Eq. (1) | `d/dU [−√(E_G/(E+U))] = ½ √E_G (E+U)^{−3/2}` | `log_rate_deriv` |
| Sec. 7.2 | The two-energy ratio cancels every energy-independent factor | `ratio_cancels` |
| Sec. 3 | 1 W at 3.65 MeV is `1.71–1.72 × 10¹²` reactions/s and `8.5–8.6 × 10¹¹` neutrons/s | `watt_reactions` |
| Sec. 8 | 1 W through 23.85 MeV is `2.6–2.7 × 10¹¹` pair creations/s | `watt_pairs` |
| Sec. 5.3 | 340 eV is 3400 phonons of 100 meV | `phonons_in_phase` |
| Sec. 7.3 | The quadrature total is `√0.000606 ∈ (0.0246, 0.0247)`; `σ_Ue ∈ (7.0, 7.1)` eV per step and `(2.8, 2.9)` eV on six steps | `quadrature_total`, `sigma_Ue` |
| Sec. 7.5 | The 100–340 eV span is resolved at more than 33σ, a 300 → 400 eV drift at more than 14σ | `discrimination` |
| Sec. 7.4 | A 3%/h drift forges about 53 eV uninterleaved over six hours, and about 0.7 eV at five-minute swaps | `drift_residuals` |

The file is [`ElectronScreening/Basic.lean`](ElectronScreening/Basic.lean). What is not proved is
in [`LIMITATIONS.md`](LIMITATIONS.md).

## How it is checked

Every push runs [the proof check](.github/workflows/build.yml): build against Lean v4.34.1 and
Mathlib v4.34.1, independent replay in Lean's kernel checker, an axiom audit (only `propext`,
`Classical.choice`, `Quot.sound`), and three deliberately false statements that must fail.

## The paper

*Electron Screening in Metal Deuterides: Measurement Systematics, Evolving Target State, and an Experimental Arbitration Protocol*, Jeromie Beasley. DOI
[10.5281/zenodo.21935285](https://doi.org/10.5281/zenodo.21935285) (always opens the newest version).

## Licence

Copyright (c) 2026 Jeromie Beasley. Code and proofs: [MIT](LICENSE). Written text:
[CC BY 4.0](LICENSE-CC-BY-4.0.md). See [`LICENSING.md`](LICENSING.md). Citation metadata is in
[`CITATION.cff`](CITATION.cff); how AI tools were used is stated in [`AI_USE.md`](AI_USE.md).
