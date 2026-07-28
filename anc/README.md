# Ancillary code — shared package of the two companion papers

*The Hodge conjecture for Fermat fourfolds of odd degree at most 199* (the note,
`../paper/boundary_note.tex`) and *Residual gap classes in the even-degree Fermat-fourfold census
through degree 250* (the companion, `../paper/even_boundary.tex`). The step table below references the
note's claims; the even-sector artifacts (steps 4–5, 8–9 and the even receipts) back the
companion's Propositions.

Standalone Python reproducing the machine-verified computations of the manuscript. Exact integer
arithmetic wherever a claim depends on it (multiset identities, Hodge grades, lattice membership,
the `Z[x]/Φ33` Frobenius certificate); no floating point enters any certificate. Every proof-critical
equality inside the scripts is an `assert`; the runner has **fresh-run semantics** (derived logs are
deleted first), so "PASSED" always means *executed now*, never cached or skipped.

## Requirements

Python 3.10+; `pip install -r requirements.txt` (exact versions pinned to the ones used for the
reported runs).

## Verification (smoke tier, ~40 s on the reference machine below)

```
sh run_all.sh
```

| step | script | manuscript claim it verifies |
|---|---|---|
| 0 | `shasum -c SHA256SUMS` | input integrity (both manuscripts at `../paper/` + every ancillary file) |
| 1 | `verify_closure_identities.py` | every exact identity of Theorems A, A′, A″ (splits, vanishing pairs, 10-multiset identities, 5-standard form, Hodge grades, the `(33,33)` self-pair) + an exchange instance at `m=110` + the Prop-D even-`m` caveat (125/125 inadmissible multisets decomposable) |
| 2 | `code/l4/census_scan_v2.py 33 39 45` | census anchors: `m=33` → the unique non-quasi non-standard witness (104 = 102 dec + 2 indec); `m=39` → both classes ∗-split; `m=45` → one two-pair class |
| 3 | `code/l4/census_scan_v3.py 33 45 66` | iterated/ledger pipeline: `45` closes (two-pair), `66` fully closes (incl. the `(33,33)` route), `33` stays open at its own level (it closes only through the level-66 lift — Thm A″) |
| 4 | `code/l4/s_lattice.py 210 1,79,...` | the degree-210 isolated class: `u ∈ S_210`, 40 generators, coefficients ±1 |
| 5 | `code/l4/s_lattice.py 70 1,20,...` | the `m=70` champion is a gap class (`u ∉ S_70`) |
| 6 | `code/l4/exact_jacobi_certificate.py` | Theorem C: exact DP in `Z[x]/Φ33` at `p=67`; the closed form `u′ = 1 + x^11`, the all-20-conjugates nontriviality, AND the exact order 6 (`(u′)^3 = −1` on every conjugate) are **asserted** |
| 7 | `code/l4/fast_close.py --calibrate` | closure-oracle calibration (5 anchored fire/no-fire cases) |
| 8 | `code/l4/census_even.py --calibrate` | even-parity census engine vs brute force, exact match `m ≤ 14` |
| 9 | `verify_lattice_witness.py` | **independent** verification of every lattice verdict in the two companion papers: the 17 OUT verdicts (8 wall members + the gap families `m=33/99/165` and `m=39/117/195`, the `105` and `168` gap classes, and the `xi_28` candidate correction) each get a *modular kernel witness* (a prime `q` and `φ` with `φ·g ≡ 0 (mod q)` for every generator and `φ·u ≢ 0`) found by this script's own elimination; the 4 IN verdicts (`210`, `39`, `45`, `105`) have their explicit certificates re-summed exactly. The engine proposes; this script decides. |
| 10 | `census_witnesses.py --verify` | re-verifies every stored per-orbit closure witness of the Theorem B census (all 89 levels: the vanishing pair / quasi split / standard parameter / ∗-split triples per orbit) and, for the seven survivor orbits, re-establishes the NEGATIVE screenings live (no pair, no quasi witness, not standard, no split) — terminal labels are re-checked certificates, not labels |
| 11 | `census_independent.py 33 39 45 105` | an algorithmically independent census reimplementation (full-unit profiles, numpy, own classifiers; no code shared with the engine) re-derives the anchor levels and asserts exact agreement with the witness receipt |
| 12 | `census_independent.py 50 70` | the same independent implementation run FRESH at the even key levels `m=50,70` (multiplicity-aware decomposability), asserted against the even receipt tier |
| 13 | `census_summary.py --check --independent 21 ... 45` | the per-level summary table (`census_level_summaries.json`: counts, tallies, survivors, canonical SHA-256 of the sorted representative list) is recomputed from the witness receipt AND regenerated from scratch by the independent implementation at every odd level `21 ≤ m ≤ 45` — the "no missed orbit" cross-check |
| 14 | `census_bruteforce.py 21 ... 45` | a THIRD method: direct exhaustive enumeration of all sorted zero-sum sextuples (no meet-in-the-middle, no shared code) reproduces the representative counts and canonical hashes at every census level `m ≤ 45`; the pinned receipt `bruteforce_odd_receipt.txt` extends this to every census level `m ≤ 143` — the range quoted in the paper |

## Reference machine and measured runtimes

All reported timings: Apple M4 Max (14 cores), 36 GB RAM, macOS 15.7, Python 3.13.13, numpy per
`requirements.txt` (the code is pure integer/numpy arithmetic — no GPU, single-process).
Measured: smoke runner ~40 s; single-level engine at the largest level `m=199`: 158 s; the
pinned two-engine 89-level receipt sweep: ≈36 min total (per-level `[m=… took …s]` lines are in
the receipt itself); complete from-scratch independent regeneration (`sh run_full_census.sh`,
all 89 levels checked against the pinned canonical hashes): ~12 min (measured 701 s). On other hardware
scale accordingly; nothing is wall-clock-sensitive (every check is an exact assert). Peak
memory: the independent implementation reaches ≈4 GB at the largest level `m=199`, and the
brute-force third method ≈2.3 GB at `m=143`; on smaller machines run the top levels
individually. The full brute-force sweep of all 61 census levels `m ≤ 143` took ≈50 min
(7-way parallel) and ships as `data/l4/bruteforce_odd_receipt.txt`.

## Census receipt (Theorem B)

Four artifacts, each SHA-pinned in `SHA256SUMS`:

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
against the pinned canonical hashes — in ~35 s; (2) the complete 89-level independent
regeneration is one command, `sh run_full_census.sh` (~12 min on the reference machine),
which must reproduce every pinned per-level count and canonical hash; the log of the campaign's
own full run ships as the checksummed receipt `data/l4/witness_independent_run.txt`. The version
pins record the environment of the reported runs; the code is pure integer arithmetic and is not
version-sensitive (nearby versions work). The even key-level
receipt (50/70/110/114/168) is pinned with its regeneration command in the receipts directory.
Fresh-vs-historical: steps 0–13 are executed now on every run; SHA-verified historical receipts
certify file integrity of the long campaign sweeps, not their fresh recomputation. `census_independent.py` (bundled, runner step 11) is an
algorithmically independent reimplementation covering all 89 levels; the original, methodologically
independent implementation used during the verification campaign is not part of this package and
not part of the reproducible chain — no claim in either paper rests on it.

## Even-sector proof objects

- `data/l4/census_receipt_even6_250.txt` — the complete fresh even census (v3 engine with ledger
  transport) over ALL even `6 ≤ m ≤ 250`. Replay:
  `python3 -c "print(' '.join(str(m) for m in range(6,251,2)))" | xargs python3 code/l4/census_scan_v3.py`
  (delete `data/l4/census_scan_v3.log` first). Expected totals: twenty-one primitive
  beyond-machinery orbits at `m ≤ 108`; seven open classes at `m ≤ 200`; ten primitive open rows
  (plus induced copies) at `m ≤ 250`, matching the manuscript's wall display and table.
- `data/l4/receipts_even/` — pinned historical logs of the exchange scan and the deep negative
  sweeps behind the wall structure (see `PROVENANCE.md` there).
- Deep-closure witnesses: the routes of `data/l4/CLOSED_LEDGER.tsv`; the ten open primitives carry
  independent modular kernel witnesses (runner step 9).

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

## Provenance

Scripts are the campaign engines used for the manuscript, byte-identical except: `obstruction105.py`
has its log path localized, and `exact_jacobi_certificate.py` had a stale unasserted sign-variant
check replaced by the asserted closed form. Engines log under `data/l4/`; `run_all.sh` deletes those
logs first, so no check is ever satisfied from cache. For *manual* engine runs note that
`census_scan_v3.py` skips an `m` already marked DONE in its own log — delete
`data/l4/census_scan_v3.log` for a clean re-run. The manuscript was prepared with AI assistance;
every computational claim quoted from the ancillary is backed by the supplied code or receipts. Repository copy: byte-identical to the shared
ancillary of the two arXiv tarballs except this README (title and manuscript paths merged for the
repository layout) and the manuscript lines of `SHA256SUMS` (`../<paper>.tex` localized to
`../paper/`); the tarballs' canonical SHA-256 hashes are pinned in the top-level README.
