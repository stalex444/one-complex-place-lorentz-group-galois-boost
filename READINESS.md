# Readiness record — one-complex-place-lorentz-group-galois-boost (2026-10-22)

Each registry rule that has cost a rejection or a failed stage before, and how it was checked
on this package. Commands are run from the package root; the Lean content is that of the first
commit (`f195e1d0`), on which the registry's pipeline was replicated locally (BUILD.txt).

1. **Challenge.lean imports Mathlib only; every definition it needs is carried inline,
   byte-for-byte consistent with the proof modules.**
   `grep -n import Challenge.lean` → the single line `public import Mathlib`. The definitions
   (`herm`, `transposeBilin`, `hsBilin`, `transposeForm`, `hsForm`, `placeMatrix`,
   `placeMatrix_isHermitian`, `placeMatrix'`, `diag_re_of_isHermitian`, `placeEquiv`,
   `PlaceSpace`, `traceB`, `bornB`, `galoisConj`, `iConj`, `boostGen`, `boostC`, `boostC_add`,
   `boostC_smul`, `boost`, `PlacePreserving`, `IsInfIsometry`, `IsIsometry`, `phaseV`, `η4`,
   `L01r … L23r`, `localGen`, `so31`, `cArith`, `Preg`, `Kmat`, `Jmat`, `blockDiag`, `coords4`,
   `Hmat`, `fromCoords`, `hodgeOp`, `HC`, `chirality`, `Pplus`, `Pminus`, `divide`, `divideFlip`,
   `iConjVec`, `L01Vec`) live in `ArithmeticLorentz/Defs.lean` (imports Mathlib only) and are
   repeated in `Challenge.lean` between `-- BEGIN SHARED DEFINITIONS` and
   `-- END SHARED DEFINITIONS`; `python3 tools/check_shared_block.py` → PASS (254 lines,
   13340 bytes identical). The scaling `S`, `η6`, the `6 × 6` generators and `IsEtaSkew4/6` are
   not needed by any compared statement and stay in the proof module. The registry's
   canonical-challenge, challenge-provenance, export and comparator stages were replicated
   locally on a fresh clone of `f195e1d0` (the record is BUILD.txt): the Challenge compiles
   outside the Lake plan with no project build directory on `LEAN_PATH`, its transitive source
   dependencies are toolchain and Mathlib only, and `lake comparator --inadvisably-no-sandbox`
   accepts in the submitted configuration and in the registry's protected configuration
   (nanoda and con-ron external kernels).

2. **The opening docstring is the scope account; it names the compared statements and their
   count exactly, and a count gate fails on mismatch.**
   The docstring says "Sixteen compared statements" and numbers them 1–16 with their Lean
   names. `python3 tools/check_count.py` → PASS: it fails (exit 1) unless the theorems declared
   in `namespace ArithmeticLorentz` of `Challenge.lean` and of `Solution.lean` equal
   `comparator.json`'s `theorem_names` in order, the docstring states the count in words and
   numbers exactly those names 1..N, `Challenge.lean` has exactly one `sorry` per compared
   theorem and none elsewhere, `Challenge.lean` imports Mathlib only, every `.lean` file carries
   the module header, `Challenge.lean` is within the registry caps (487 lines, 29184 bytes; caps
   1000 lines, 100 KiB), and `formalization.yaml`'s `alignment.statements` list the same names in
   order. Negative test: renaming one statement in a scratch copy makes it exit 1.

3. **Every path cited in README.md and formalization.yaml exists at the commit.**
   Checked with `git ls-tree -r --name-only HEAD` against every backticked `*.lean`, `*.py`,
   `*.json`, `*.yaml`, `*.yml`, `*.md`, `*.txt` path in README.md, formalization.yaml and the
   Challenge docstring (`ArithmeticLorentz/*.lean`, `tools/*.py`, `Challenge.lean`,
   `Solution.lean`, `comparator.json`, `formalization.yaml`, `BUILD.txt`, `SHA256SUMS.txt`,
   `READINESS.md`, `LICENSE`, `.github/workflows/palomar-preflight.yml`). Paths of the form
   `Mathlib/…` are Mathlib's at the pinned commit (checked in the pinned checkout), and the two
   register paths (`Challenge.lean` lines 35–75, `GravityScreening/HodgeBulkScreen.lean`) are
   those of `stalex444/pdt-hodge-lie-generation` at `e2d8dde` (checked with `git ls-tree` on
   that commit). `.gitignore` lists `/.lake` and `/notes` only; nothing cited is ignored.

4. **Classification.** `classification.arxiv: ["math.RT", "math.NT", "math-ph", "gr-qc",
   "cs.LO"]`; `msc2020: ["11R04", "11E10", "22E43", "15A63", "83A05", "68V20"]`. Theorem first,
   physics as the cited application (the last paragraph of the Challenge docstring, the
   "Application" section of README.md, the end of the yaml description).

5. **Prior-art guards in the docstring, no "first" claims.** The docstring's paragraph "What is
   classical, and is not this structure" states: `Herm₂(ℂ) ≅ ℝ^{3,1}` via `det` with the spinor
   action `X ↦ A X A†` is classical (Jordan–von Neumann–Wigner 1934; Penrose–Rindler 1984) and
   is not this structure — here the form is `tr(X Xᵀ)` with `σ_y` timelike and the boost is
   `i ∘ Galois conjugation`; the Hodge dual of a boost being a rotation is textbook; the
   contribution is which boost and which rotation in place coordinates. It also discloses
   Taussky 1968 for the trace-form type and Banaszak et al. 2012 as the nearest "arithmetic
   qubit" statement. `grep -in "first" Challenge.lean README.md formalization.yaml` finds no
   priority claim: the word occurs twice, in ordinary prose (README: "whose first theorem is
   statement 2"; yaml: "Statements fixed first from a target list"), and not at all in
   `Challenge.lean`.

6. **Shared Mathlib pin.** `lean-toolchain` = `leanprover/lean4:v4.35.0-rc2`;
   `lake-manifest.json` = the scratch package's manifest with the package name changed
   (Mathlib `065356127b1dc0016f66b7283ce0ce2c4055aa55`, same revisions for every dependency as
   `coxeter-growth`); `.lake/packages` is a symlink to `coxeter-growth/.lake/packages` (ignored).
   Plain `lake build` from a fresh clone with that symlink: Build completed successfully
   (8944 jobs), about one minute wall clock.

7. **Short SHAs copied from `git rev-parse --short=8`.** `f195e1d0` (first commit, the Lean
   content) was printed by that command and pasted; the second commit's SHA is reported by the
   same command after this file is committed and is not written into any shipped file.

Further checks
- `lake build` (default targets `ArithmeticLorentz`, `Challenge`, `Solution`): exit 0; the only
  warnings are the 16 `declaration uses sorry` of the Challenge placeholders (the proof modules
  build with no warnings after the linter sweep).
- `#print axioms` through `Solution` for all 16 compared names: each exactly
  `[propext, Classical.choice, Quot.sound]` (BUILD.txt).
- `sorry` count: Challenge.lean 16; every other file 0. `native_decide`: 0. `axiom`: 0.
- `Solution.lean` is generated from the same statement text as `Challenge.lean` (each `sorry`
  replaced by `exact` of one proof-module theorem), so the compared statements are identical by
  construction; the kernel accepted every `exact`.
- `formalization.yaml` validates against the registry's dispatcher schema and its v0.4 schema
  (mathlib-initiative/formalization.yaml) with 0 errors. The schema's `relationship` enum has no `uses`; the
  register entry PALOMAR-2026-09-30-000024 is listed as `builds-on` with the note "used as
  cited data".
- Reviewer-facing text: no internal-process wording (swept for working-file names, run labels
  and process terms in every shipped `.lean`, `.md`, `.yaml`, `.json`).
- Bibliographic identifiers checked against Crossref on 2026-10-22: JNW 1934 (10.2307/1968117),
  Taussky 1968 (10.1112/jlms/s1-43.1.152), Banaszak et al. 2012 (10.12693/APhysPolA.121.1111),
  Holst 1996 (10.1103/PhysRevD.53.5966). Penrose–Rindler 1984 and Baez 2002 are cited by book
  DOI and arXiv id without the texts being opened.

What is not settled by this record (for the author)
- The application paragraph (Challenge docstring, README, yaml) is a draft for the author to
  edit.
- The register is cited as PALOMAR-2026-09-30-000024 (`pdt-hodge-lie-generation` @ `e2d8dde`),
  which is where both files used (`Challenge.lean`, `GravityScreening/HodgeBulkScreen.lean`)
  resolve. A second register entry number (000035) was mentioned in the packaging request; no
  entry with that number could be identified from the local records, so it is not cited. If the
  Hodge-divide operators were registered separately under that number, add it to
  `related_formalizations` and to the README's "The author's registered entries" paragraph.
- Compared set: the request listed `transposeForm_phaseAd_invariant_iff` with
  `traceB_phaseV_iff` as the alternative; the former needs `phaseAd` from the polar-phase
  module of the source development, which is outside this entry's module set, so the
  place-coordinate form `traceB_phaseV_iff` is compared (statement 8), re-proved here without
  that module. The item "hermitian_exclusion / sigNeg_transposeForm_eq_one_iff" is compared as
  two declarations (statements 1 and 2), giving sixteen; drop one and re-run
  `tools/check_count.py` after editing the docstring count if fifteen is preferred.

## 2026-10-22 · submission-form fix
The registry's form rejected the first submission attempt: "source-based results need a formalizes, adapts, or independently-proves source" (all seven sources were `background`). Fixed by adding an `original-proof` source as the first entry (relationship `other`, author_endorsement `participated`, location README.md), the form used by the registered PALOMAR-2026-09-30-000024. Lean content unchanged (f195e1d0).
