# The Positive Defect Problem: Target and Admissibility Criteria for a Programmatic Search for Unforced Navier-Stokes Blowup

J. Petrillo and J. Glimm. Standalone repository containing the paper and the Lean 4 library it cites.

## Contents

| Path | What |
|---|---|
| `reduction.tex`, `reduction.bib`, `reduction.pdf` | The paper (two-column; 7 pp at the last build, 2026-09-09 WRITE-B10: body through p. 6, bibliography pp. 6–7). Build: `bash compile.sh`. |
| `EnergyDefect/*.lean`, `EnergyDefect.lean` | The Lean 4 library in the single namespace `EnergyDefect` — exactly the modules whose theorems the paper cites, with their dependencies. No `sorry`, no custom axioms. After the 2026-09-16 restoration of §5 "The Search: Persistence in Time, Not in Scale" the paper cites 35 declarations in 11 modules; the package is their closure: **17 modules, 88 theorem/lemma declarations**, regenerated 2026-09-16 with `tools/build_reduction_package.py`. **Not yet rebuilt with `lake build` after the regeneration** (the previous 15-module package built clean, 2728 jobs, 2026-09-09; the two returning modules built clean in the 2026-09-05 package). |
| `lakefile.toml`, `lake-manifest.json`, `lean-toolchain` | Pinned toolchain: Lean v4.33.0, Mathlib v4.33.0. |
| `LICENSE`, `NOTICE`|


## Intro

The paper is framed from the start by the constructions announced on 7–8
September 2026 — a forced Navier-Stokes singularity at every fixed viscosity
(Clay (C)/(D)) and Euler singularities, produced, per the OpenAI announcement,
by a system of coordinating agents — and by what remains open after them: the
unforced problem, Clay (A)/(B). It fixes the target for one route to that
problem — the positive defect problem of §2 — and supplies what a programmatic
search along that route requires: one machine-checked target, proven necessary
conditions on any admissible candidate, and proven statements of what cannot
certify one. The announced constructions are placed against the conditions at
the end of §4 (forced; Type II in velocity; core energy → 0; energy at the
singular time not discussed; not a candidate).

The paper proves an equivalence for Leray-Hopf solutions of the incompressible
Navier-Stokes equation on the periodic cube (Thm 3.2): a floor on the rate of
energy transfer to fine scales, averaged over a finite window, holds if and
only if the solution has a **positive defect** on that window — a strict
energy inequality at fixed viscosity. This is the positive defect problem,
question (a) of Duchon and Robert (2000) for smooth data; it is open, it
implies finite-time blowup, and it is not known to follow from blowup.
Delimiting results say what a proof must produce (§4: a jump of the kinetic
energy at a Type II singular time; Type I and self-similar blowup excluded;
the Chae–Wolf gradient-rate transfer; the pressure exit; the super-diffusive
scale; no known steady Euler profile; Tao's averaged model has no such jump up
to its blowup time, argued from that paper's bounds) and what cannot supply
one (§5: finite computation, selection principles, forcing). The unforced
questions (A)/(B) remain open as well; a positive defect would answer (B) in
the negative, and the paper's target statement, necessary conditions, and
no-go results are the specification and admissibility criteria for a
programmatic search that approaches (A)/(B) through a positive defect (§1,
§6).

The target is the floor hypothesis of the floor-ceiling argument for
finite-time loss of regularity (Glimm–Petrillo, arXiv:2410.09261) in averaged
form; the pointwise floor the argument itself uses implies it (Thm 3.2(b)).
The argument confines the rate of energy transfer between a floor and a
ceiling decaying strictly faster, and it is the motivation, not a claim of
this paper: its arithmetic is stated in one sentence of §2 (with its three
Lean tags), every implication not marked otherwise is formalized in Lean 4 and
compiles from the standard axioms (five steps in §4 are marked "argued, not
formalized"), and the paper makes no claim about the argument's conclusion.

## Verifying the Lean library

```sh
lake exe cache get   # Mathlib build cache
lake build           # builds EnergyDefect (≈ 2700 jobs with the cache)
```

Every theorem tagged `[L: name]` in the paper resolves to the declaration
`EnergyDefect.name` in `EnergyDefect/*.lean`. Check any theorem's axioms with

```lean
import EnergyDefect
#print axioms EnergyDefect.averaged_tail_floor_le_defect
-- [propext, Classical.choice, Quot.sound]
```

File guide (paper section → file): the floor-ceiling arithmetic (§2, one
sentence, three tags) `Blowup.lean`, `Interface.lean`, `HardyRoute.lean`;
the shell balance, the equivalence, and defect maximization (Lemma 3.1,
Thm 3.2, §5 Selection) `EnergyDefect.lean` (with `ErgodicFusion.lean`); the
defect as a jump and the covering lemma (Thm 4.1, §4 item 3)
`EnergyProfile.lean`; the super-diffusive scale and the steady-profile
obstruction (§4 item 6) `SuperDiffusiveAtom.lean`, `JordanObstruction.lean`;
unwitnessable ceilings (Thm 5.1) `GapOneInterface.lean`,
`ValidatedProof.lean` (with `JensenCeiling.lean`); forcing (§5)
`StationaryFlux.lean`; `OnsagerRoute.lean`, `Sharpening.lean` and
`GenusThreshold.lean` are dependencies; the certified margin and the lag
model (§5 The Search, eq. (simult), Thm 5.2) `PeakSimultaneity.lean`
(with `CascadeFront.lean`), returned to the package 2026-09-16 when that
paragraph was restored. `LocalDefect.lean` is not cited and is not in the
package.

The library is generated from the authors' full development (147
theorem/lemma declarations after the six of §4 item 6, 2026-09-08) by `tools/build_reduction_package.py` in the development
repository; the flat single-namespace layout here is the distributed form.

