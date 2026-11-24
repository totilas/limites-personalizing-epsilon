# Bridge: our Rényi divergence vs Statlib

A cross-check of the main project's definition of the Rényi divergence against an
independent one: the `renyiDiv` of [Statlib](https://github.com/stat-lib/statlib),
which absorbed R. Degenne and L. Luccioli's
[TestingLowerBounds](https://github.com/RemyDegenne/testing-lower-bounds) project.

```lean
theorem RenyiBridge.renyiDiv_eq_statlib
    [IsProbabilityMeasure P] [IsProbabilityMeasure Q] (hα : 1 < α) :
    Limites.renyiDiv α P Q = (ProbabilityTheory.renyiDiv α P Q : EReal)
```

For probability measures and every order α > 1, the orders zCDP uses, the two
definitions agree. Statlib's `renyiDiv` takes values in `ℝ≥0∞` and is defined for
all finite measures (through the Hellinger divergence of the normalized measures);
ours takes values in `EReal`, hence the coercion.

**Why a separate project.** Statlib is on Lean v4.37.0-rc1, the main project on
v4.33. This project pins Statlib (commit `8c95743`, 2026-11-22) and its Mathlib, and
contains verbatim copies of the two main-project files the bridge needs
(`LimitesProofs/Privacy/Defs.lean`, `LimitesProofs/Renyi.lean`). Run
`./check-sync.sh` to check that the copies are identical to `../../lean`.

```bash
lake exe cache get
lake build
```
