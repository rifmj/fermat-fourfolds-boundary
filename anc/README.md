# Ancillary code — shared package of the two companion papers

*The Hodge conjecture for Fermat fourfolds of odd degree at most 199* (the note)
and *Residual gap classes in the even-degree Fermat-fourfold census through degree 250* (this
submission's manuscript, `../even_boundary.tex`). The step table below references the
note's claims; the even-sector artifacts (steps 4–5, 8–9 and the even receipts) back the
companion's Propositions.

Standalone Python reproducing the machine-verified computations of the manuscript. Exact integer
arithmetic wherever a claim depends on it (multiset identities, Hodge grades, lattice membership,
the `Z[x]/Φ33` Frobenius certificate); no floating point enters any certificate. Every proof-critical
equality inside the scripts is an `assert`; the runner has **fresh-run semantics** (derived logs are
deleted first), so "PASSED" always means *executed now*, never cached or skipped.

## Requirements

Python 3.10+ and NumPy (plus `mpmath` for the one 30-digit corroboration in step 6). Three
version tiers, deliberately distinguished:

- **Required (minimum):** Python ≥ 3.10, NumPy ≥ 1.22, mpmath ≥ 1.2. Nothing here depends on
  recent library behaviour — every proof-critical computation is exact integer arithmetic.
- **Used for the reported runs (pinned):** the exact versions in `requirements.txt`
  (`pip install -r requirements.txt` reproduces them); these are the versions behind every
  shipped receipt.
- **Additionally tested:** nearby releases of NumPy on the same code path give identical output;
  the checks are exact equalities, so agreement is bit-for-bit rather than approximate.

## Verification (smoke tier, ~43 s on the reference machine below)

```
sh run_all.sh
```

| step | script | manuscript claim it verifies |
|---|---|---|
| 0 | `shasum -c SHA256SUMS` | input integrity (manuscript at `../even_boundary.tex` + every ancillary file) |
| 1 | `verify_closure_identities.py` | every exact identity of Theorems A, A′, A″ (splits, vanishing pairs, 10-multiset identities, 5-standard form, Hodge grades, the `(33,33)` self-pair) + an exchange instance at `m=110` + the Prop-D even-`m` caveat (125/125 inadmissible multisets decomposable) |
| 2 | `code/l4/census_scan_v2.py 33 39 45` | census anchors: `m=33` → the unique non-quasi non-standard witness (104 = 102 dec + 2 indec); `m=39` → both classes ∗-split; `m=45` → one two-pair class |
| 3 | `code/l4/census_scan_v3.py 33 45 66` | iterated/ledger pipeline: `45` closes (two-pair), `66` fully closes (incl. the `(33,33)` route), `33` stays open at its own level (it closes only through the level-66 lift — Thm A″) |
| 4 | `code/l4/s_lattice.py 210 1,79,...` | the degree-210 isolated class: `u ∈ S_210`, 40 generators, coefficients ±1 |
| 5 | `code/l4/s_lattice.py 70 1,20,...` | the `m=70` champion is a gap class (`u ∉ S_70`) |
| 6 | `code/l4/exact_jacobi_certificate.py` | Theorem C: exact DP in `Z[x]/Φ33` at `p=67`; the closed form `u′ = 1 + x^11`, the all-20-conjugates nontriviality, AND the exact order 6 (`(u′)^3 = −1` on every conjugate) are **asserted** |
| 7 | `code/l4/fast_close.py --calibrate` | closure-oracle calibration (5 anchored fire/no-fire cases) |
| 8 | `code/l4/census_even.py --calibrate` | even-parity census engine vs brute force, exact match `m ≤ 14` |
| 9 | `verify_lattice_witness.py` | **independent** verification of every lattice verdict in the two companion papers: the 17 OUT verdicts (8 wall members + the gap families `m=33/99/165` and `m=39/117/195`, the `105` and `168` gap classes, and the `xi_28` candidate correction) each get a *modular kernel witness* (a prime `q` and `φ` with `φ·g ≡ 0 (mod q)` for every generator and `φ·u ≢ 0`) found by this script's own elimination; the 7 IN verdicts have their explicit certificates re-summed exactly. The engine proposes; this script decides. |
| 10 | `census_witnesses.py --verify` | re-verifies every stored per-orbit closure witness of the Theorem B census (all 89 levels: the vanishing pair / quasi split / standard parameter / ∗-split triples per orbit) and, for the seven survivor orbits, re-establishes the NEGATIVE screenings live (no pair, no quasi witness, not standard, no split) — terminal labels are re-checked certificates, not labels |
| 11 | `census_independent.py 33 39 45 105` | an algorithmically independent census reimplementation (full-unit profiles, numpy, own classifiers; no code shared with the engine) re-derives the anchor levels and asserts exact agreement with the witness receipt |
| 12 | `census_independent.py 50 70` | the same independent implementation run FRESH at the even key levels `m=50,70` (multiplicity-aware decomposability), asserted against the even receipt tier |
| 13 | `census_summary.py --check --independent 21 ... 45` | the per-level summary table (`census_level_summaries.json`: counts, tallies, survivors, canonical SHA-256 of the sorted representative list) is recomputed from the witness receipt AND regenerated from scratch by the independent implementation at every odd level `21 ≤ m ≤ 45` — the "no missed orbit" cross-check |
| 14 | `census_bruteforce.py 21 ... 45` | a THIRD method: direct exhaustive enumeration of all sorted zero-sum sextuples (no meet-in-the-middle, no shared code) reproduces the representative counts and canonical hashes at every census level `m ≤ 45`; the pinned receipt `bruteforce_odd_receipt.txt` extends this to every census level `m ≤ 143` — the range quoted in the paper |
| 15 | `even_tier_table.py --check` | the even-sector TIER table (`even_tier_table.json`): every level `m ≤ 60` is RECOMPUTED from the definitions and asserted identical to the stored row; for all 123 levels the stored counts and the canonical SHA-256 of each survivor list are re-derived from the stored class lists. A full from-scratch rebuild of every level is `--emit` (hours; the largest levels dominate) |
| 16 | `even_final_table.py --check` | the complete reader's table (`even_final_table.json`): all 40 primitive post-depth-two survivors with content, exact lattice verdicts (`ν∈S_m`, `2ν∈S_m`), status and route; every verdict recomputed here by an independent HNF test, the 8 open classes asserted to be gap classes |
| 17 | `verify_w168_witness.py` | Proposition w168 end to end: `a` and `beta` are Hodge (2,2) characters over ALL units, `beta` is *-split (6+54+108=168, 60+126+150=336), `ν(a)−ν(beta) ∈ S₁₆₈` with both individually OUTSIDE (non-vacuity), `2ν(a) ∈ S₁₆₈`, the stored integer certificate re-summed from disk (94 coefficients in [−3,3] over the generator list) and the modular kernel witness that separates BOTH `ν(a)` and `ν(β)` from S₁₆₈, and the control that `a` itself is not *-split |
| 18 | `obstruction105.py calib` | the Theorem-C Frobenius certificate recomputed by a SECOND independent implementation (different reduction basis) |
| 19 | `verify_deep_routes.py` | every deep-closure route in `CLOSED_LEDGER.tsv` that carries an explicit witness is re-verified from the definitions: the listed pairs really vanish, the multiset identity `class ⊎ pairs = blocks` holds exactly, and every block is re-derived (grade-2 Hodge quadruple / grade-3 sextuple that is itself base-closed). Rows carrying only a label are reported as such, not counted as verified |

## Reference machine and measured runtimes

All reported timings: Apple M4 Max (14 cores), 36 GB RAM, macOS 15.7, Python 3.13.13, numpy per
`requirements.txt` (pure integer/numpy arithmetic). No GPU is required. Most individual
verifiers are single-process; the closure calibration (`fast_close.py`) uses a
`multiprocessing.Pool`, and the archived full brute-force campaign was run with external CPU
parallelism (one process per level).
Measured: smoke runner 43 s (19 steps, timed run); single-level engine
at the largest level `m=199`: 158 s; the
pinned two-engine 89-level receipt sweep: ≈36 min total (per-level `[m=… took …s]` lines are in
the receipt itself); complete from-scratch independent regeneration (`sh run_full_census.sh`,
all 89 levels checked against the pinned canonical hashes): ~12 min (measured 701 s). On other hardware
scale accordingly; nothing is wall-clock-sensitive (every check is an exact assert). Peak
memory: the independent implementation reaches ≈4 GB at the largest level `m=199`, and the
brute-force third method ≈2.3 GB at `m=143`; on smaller machines run the top levels
individually. The full brute-force sweep of all 61 census levels `m ≤ 143` took ≈1 h
(7-way parallel, peak RSS ≈3.2 GB at the top levels) and ships as
`data/l4/bruteforce_odd_receipt.txt`, with the full canonical SHA-256 printed per level.

## Census receipt (Theorem B)

Seven artifacts, each SHA-pinned in `SHA256SUMS`:

- `data/l4/census_receipt_odd21_199.txt` — the complete fresh run of both census engines over all
  89 odd levels `21 ≤ m ≤ 199`, `m ≠ 23` (the omitted small levels are classical): per-level
  representative counts, classification tallies, and every surviving orbit.
- `data/l4/census_witnesses_odd.json` — the WITNESS tier: for every one of the ~89-level orbit
  representatives, its classification together with an explicit, machine-verified witness
  (`census_witnesses.py`; every witness is asserted at emission and re-asserted by runner step 10).
- `data/l4/witness_independent_run.txt` — the full run of the independent reimplementation
  (`census_independent.py`) over all 89 levels, asserting exact agreement with the witness receipt
  level by level.
- `data/l4/census_level_summaries.json` — the per-level summary table: representative count,
  tally by kind, survivor list, and the SHA-256 of the canonically sorted representative list.
  Rebuild: `python3 code/l4/census_summary.py --emit`; check: `--check`; regenerate any level
  from scratch against it: `--independent <m ...>` (runner step 13 does all odd `21 ≤ m ≤ 45`;
  `run_full_census.sh` does all 89 levels).
- `data/l4/even_tier_table.json` — the even-sector tier table: for every even `6 ≤ m ≤ 250`,
  the representative count, the base-tier survivor count, the post-depth-two survivor count
  (the paper's headline tier), the survivor classes and the canonical SHA-256 of that level's
  survivor list. Rebuild any level: `python3 code/l4/even_tier_table.py --emit <m ...>`;
  check: `--check` (runner step 15). Base-tier survivors begin at `m=32` and number 1349
  through 250; the post-depth-two tier is the 40 classes of the paper.
- `data/l4/even_final_table.json` — those 40 classes one by one: content, exact `ν∈S_m` and
  `2ν∈S_m` verdicts, status (deep-closed / closed-by-proposition / open) and route; verified
  by `even_final_table.py --check` (runner step 16), which recomputes every lattice verdict.
- `data/l4/bruteforce_odd_receipt.txt` — the brute-force (third-method) run over EVERY census
  level `21 ≤ m ≤ 143`: counts and canonical hashes reproduced by direct exhaustive
  enumeration. Regenerate any level: `python3 code/l4/census_bruteforce.py <m ...>` (runner
  step 14 re-runs `m ≤ 45` live on every invocation).

Regenerate the engine receipt:

```
python3 -c "print(' '.join(str(m) for m in range(21,200,2) if m!=23))" | xargs python3 code/l4/census_scan_v2.py
```

(and the same for `census_scan_v3.py`). Reproducibility tiers: (1) the smoke runner above executes
every check live — all 78,299 stored witnesses (incl. the survivor negative screenings), the
anchor-level independent census, and a fresh independent regeneration of every odd level ≤ 45
against the pinned canonical hashes, and the direct brute-force generator on every census
level through `m = 45` — in ~43 s; (2) the complete 89-level independent
regeneration is one command, `sh run_full_census.sh` (~12 min on the reference machine),
which must reproduce every pinned per-level count and canonical hash; the log of the campaign's
own full run ships as the checksummed receipt `data/l4/witness_independent_run.txt`. The version
pins record the environment of the reported runs; the code is pure integer arithmetic and is not
version-sensitive (nearby versions work). The even key-level
receipt (50/70/110/114/168) is pinned with its regeneration command in the receipts directory.
Fresh-vs-historical: steps 0–19 are executed now on every run; SHA-verified historical receipts
certify file integrity of the long campaign sweeps, not their fresh recomputation. `census_independent.py` (bundled, runner step 11) is an
algorithmically independent reimplementation covering all 89 levels; the original, methodologically
independent implementation used during the verification campaign is not part of this package and
not part of the reproducible chain — no claim in either paper rests on it.

## Even-sector proof objects

- `data/l4/census_receipt_even6_250.txt` — the complete fresh even census (v3 engine with ledger
  transport) over ALL even `6 ≤ m ≤ 250`. Replay:
  `python3 -c "print(' '.join(str(m) for m in range(6,251,2)))" | xargs python3 code/l4/census_scan_v3.py`
  (delete `data/l4/census_scan_v3.log` first). Expected totals: twenty-one
  primitive post-depth-two survivors at `m ≤ 108`, forty through `m ≤ 250`; ten primitive
  residual rows after the deep tiers, matching the manuscript's wall display and table.
  Vocabulary, used consistently: the RESIDUAL after the deep tiers is **ten** primitive classes;
  the two closed by the paper's propositions leave **eight** FINAL open classes. "ν ∉ S_m" holds
  for those eight (the `m=210` class `(1,79,109,121,151,169)` is in the residual ten but has
  ν ∈ S₂₁₀ — which is exactly why the proposition closes it).
- `data/l4/receipts_even/` — pinned historical logs of the exchange scan and the deep negative
  sweeps behind the wall structure (see `PROVENANCE.md` there).
- Deep-closure witnesses: the routes of `data/l4/CLOSED_LEDGER.tsv`; the eight FINAL open
  primitives carry independent modular kernel witnesses (runner step 9). Of the two residual
  classes the propositions close, the `m=168` one also carries a non-membership witness (plus the
  transportable coset certificate of step 17), while the `m=210` one carries a re-summed
  MEMBERSHIP certificate — its ν lies in S₂₁₀, so a non-membership witness cannot exist.

## Full tier (hours; the deep negative sweeps)

- Even census and the `≤ 250` boundary: `census_even.py <m...>`, `census_scan_v3.py <m...>`.
- Exchange/wall structure: `exchange_close.py <m>`; iterated closures: `survivors_iterate.py`;
  level-lift sweeps: `lift_sweep.py`; `m=33` own-level exhaustion: `predicates33_depth3.py`.
- Field obstructions at arbitrary `(m, p, class)`: `obstruction105.py run <m> <p> <label>`
  (kernel primes exist — e.g. `m=33, p=859` gives `u = 1` on every conjugate; the paper's
  obstruction uses `p=67`, where every value is a primitive 6th root).

## Data artifacts

- `data/l4/CLOSED_LEDGER.tsv` — the deep-closure ledger (route + provenance per class) consumed by
  `census_scan_v3.py` transport post-processing.
- `data/l4/P1_certificate.json` — the stored 40-generator certificate for the degree-210 class
  (re-derived live by steps 4 and 9).
- `data/l4/census_receipt_odd21_199.txt` — the Theorem B census receipt (above).

## License

`LICENSE` in this directory: MIT for the code (`.py`, `.sh`), CC BY 4.0 for the data, receipts
and documentation. At acceptance the package is additionally deposited under a permanent
identifier (DOI) as an immutable release carrying the checksums of this submission.

## Provenance

Scripts are the campaign engines used for the manuscript, byte-identical except: `obstruction105.py`
has its log path localized, and `exact_jacobi_certificate.py` had a stale unasserted sign-variant
check replaced by the asserted closed form. Engines log under `data/l4/`; `run_all.sh` deletes those
logs first, so no check is ever satisfied from cache. For *manual* engine runs note that
`census_scan_v3.py` skips an `m` already marked DONE in its own log — delete
`data/l4/census_scan_v3.log` for a clean re-run. The manuscript was prepared with AI assistance;
every computational claim quoted from the ancillary is backed by the supplied code or receipts.
