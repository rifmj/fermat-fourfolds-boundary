# Fermat fourfolds: the Hodge conjecture in odd degree ≤ 199, and the even-degree census through 250

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.21670577.svg)](https://doi.org/10.5281/zenodo.21670577)

Papers, exact-arithmetic verification package, census certificates, and Lean formalisation for
the companion pair

> R. Jumagulov, *The Hodge conjecture for Fermat fourfolds of odd degree at most 199* (2026).
> arXiv id pending.

> R. Jumagulov, *Residual gap classes in the even-degree Fermat-fourfold census through
> degree 250: exchange walls and two closures* (2026). arXiv id pending; the companion of
> the note — the ancillary package is shared.

**Result (the note).** For the Fermat fourfold `X_m^4 : x_0^m + … + x_5^m = 0 ⊂ P^5` the Hodge
conjecture holds for **every odd degree `m ≤ 199`** — a computer-assisted proof combining
three geometric closure criteria with an exhaustive machine census of the Hodge
`(2,2)`-orbits. The three closure mechanisms:

- **∗-split transport** — if the character multiset splits into two zero-sum triples, the
  rational Hodge block is transported from a `(1,1)`-substructure of a product of Fermat curves,
  hence algebraic;
- **two-pair completion** — algebraicity follows for characters that, after adjoining two
  vanishing pairs, decompose into an Aoki standard sextuple and a grade-2 Hodge quadruple;
- **level-66 descent** — the exceptional class at `m = 33` has a quasi-decomposable lift to
  level 66, and its algebraicity descends along the finite morphism `X_66^4 → X_33^4`.

Together with the known decomposable / quasi-decomposable / standard cases these cover all odd
degrees `m ≤ 199`. The census runs over the 89 machine-examined levels `21 ≤ m ≤ 199`, `m ≠ 23`
(smaller odd degrees and `m = 23` are classical), classifies all 78,299 Galois-orbit
representatives, and isolates thirteen orbits beyond decomposability, quasi-decomposability,
and Aoki's standard cycles — six close by the ∗-split criterion, the remaining seven by the
two-pair and level-lifted closures, leaving none. Every classification carries a machine-checked
witness (positive for the classified orbits, re-established negative screenings for the terminal
ones), with a completeness proof for the enumeration, and it is reproduced by two further
implementations: an algorithmically independent census over all 89 levels and a direct
brute-force enumeration through `m = 143`. Seven of the thirteen are gap classes outside Aoki's
standard lattice calculus and are new to the author's knowledge; for the other six,
algebraicity is also derivable from that calculus — the explicit presentations given here being
the new content. An exact Jacobi-sum computation at `p = 67`
(Theorem C) shows no cycle defined over `Q(ζ_33)` projects nontrivially onto the exceptional
`m = 33` block; over any finite extension of `Q(ζ_33)` carrying a certifying cycle, every residue degree
above 67 is divisible by 6.

**Result (the companion).** The even-degree sector through `m ≤ 250` behaves differently: gap
classes are frequent and the odd law "survivor ⟹ 3|m" fails. The companion identifies the
working lattice with Aoki's group `S_m` generator-by-generator, proves a negation-closure lemma
turning integer membership certificates into literal Aoki claim chains, and runs the even-parity
census: forty primitive classes survive the four base predicates and the complete depth-`≤2`
closure oracle, all but ten closed by deeper partition certificates. An exchange theorem plus an
exhaustive scan organizes the ten into five walls; two close, both by a coset-transfer lemma
internal to the two-paper package (the `m = 168` class is congruent modulo `S_168` to an explicit
`*`-split class; the isolated `m = 210` class lies in `S_210` itself, by an explicit 40-generator
`±1` certificate displayed in full). The residual even-degree boundary at `m ≤ 250` is **eight certified gap classes in
three exchange walls `W_70`, `W_110`, `W_114`**; every lattice verdict carries an independent
certificate (modular kernel witnesses for non-membership, exact re-summation for membership).

> **Papers:** [`paper/boundary_note.pdf`](paper/boundary_note.pdf) (19 pp) ·
> [`paper/even_boundary.pdf`](paper/even_boundary.pdf) (12 pp) — sources alongside.

## Verification

The shared ancillary (`anc/`) is standalone Python with exact integer arithmetic wherever a
claim depends on it; every proof-critical equality is an `assert`, and the runner has
**fresh-run semantics** (derived logs are deleted first, so "PASSED" always means *executed
now*, never cached):

    cd anc
    python3 -m venv venv && source venv/bin/activate
    pip install -r requirements.txt          # pinned; nearby versions work (pure integer/numpy)
    sh run_all.sh                            # smoke tier; measured runtime in anc/README.md

Highlights of the 19-step runner (full script ↔ claim map in [`anc/README.md`](anc/README.md)):

| step | verifies |
|---|---|
| 1 | every exact identity of Theorems A, A′, A″ + an exchange instance + the Prop-D even-`m` caveat |
| 6 | Theorem C: exact dynamic programming in `Z[x]/Φ33` at `p = 67`; closed form `u′ = 1 + x^11`, all-20-conjugates nontriviality, and the exact order 6 are asserted |
| 9 | **independent** verification of every lattice verdict in both papers — 17 OUT verdicts each get a modular kernel witness found by this script's own elimination; the 7 IN certificates are re-summed exactly |
| 10 | every stored per-orbit closure witness of the Theorem B census (all 89 odd levels), incl. live re-establishment of the survivor **negative** screenings |
| 11–12 | an algorithmically independent census reimplementation re-derives the anchor levels (odd) and the even key levels fresh, asserted against the receipts |
| 13 | the per-level summary table is recomputed from the witness receipt AND regenerated from scratch at every odd level `21 ≤ m ≤ 45` |
| 14 | a **brute-force third method** (direct exhaustive enumeration, no shared code with either census implementation) re-derives every census level `m ≤ 45` |
| 15–16 | the companion's even-sector tables recomputed: per-level base / post-depth-two counts with canonical hashes, and the final 40-row table — every lattice verdict recomputed, eight open gap classes |
| 17 | the `m = 168` closure witness: grades, the two split sums, the coset membership, non-vacuity |
| 18 | Theorem C re-verified by a **second independent implementation** (different reduction basis) |
| 19 | every deep-closure route of the ledger re-verified **from the definitions** — vanishing pairs, the exact multiset identity, each block re-derived |

Full tier: `sh run_full_census.sh` — the complete from-scratch independent regeneration of all
89 odd levels against the pinned canonical hashes (~12 min on the reference machine; peak
memory ≈4 GB at `m = 199`, and ≈2.3 GB for the brute-force method at `m = 143` — see
`anc/README.md`); the even census replay command (`6 ≤ m ≤ 250`) and the deep-sweep entry
points are in `anc/README.md`.

## Lean formalisation (`lean/`)

Machine-checks the note's combinatorial/arithmetic core **and its deduction chains**, in the
two-tier style of the surface companion's repository
([rifmj/fermat-ns-ranks](https://github.com/rifmj/fermat-ns-ranks), arXiv:2607.17387), plus a
new middle tier — a **claim calculus** certifying the citation chains themselves. No `sorry`,
no `axiom` declarations. See [`lean/README.md`](lean/README.md).

- [`BoundaryData.lean`](lean/BoundaryData.lean) — generated data (kernel witnesses, integer
  certificates, exchange edges); **untrusted input**, everything is re-verified in Lean
  (generator: `gen_data.py` from `lean_data.json`).
- [`BoundaryCore.lean`](lean/BoundaryCore.lean) — Tier 1: the finite receipts in-kernel
  (`native_decide`), ≈ the ancillary smoke tier.
- [`BoundaryClaim.lean`](lean/BoundaryClaim.lean) — Tier 2: the claim calculus — the
  manuscript's deduction chains as machine-checked derivations, sound for any predicate
  satisfying the ten cited inputs.
- [`BoundaryValidity.lean`](lean/BoundaryValidity.lean) — Tier 2 receipts: the validity guards
  of the calculus, proved with **standard axioms only** (every derivable class has ≥ 2 entries —
  no rule ever speaks about an object outside the cited literature).
- [`BoundaryForms.lean`](lean/BoundaryForms.lean) — Tier 3: two `∀`-lemmas in mathlib v4.32.0
  (standard axioms; grade-constancy ⟹ length `2g`; Prop D for every unit `t`).

Build: `lake exe cache get && lake build` (only Tier 3 needs mathlib; Tiers 1–2 compile with a
bare toolchain — see `lean/README.md`).

## Integrity chain

The top-level [`SHA256SUMS`](SHA256SUMS) pins both paper sources and `anc/SHA256SUMS`, which
pins every ancillary file. The arXiv source packages built from this tree (not yet posted; not tracked in this repository) are pinned by

    6e70cc887a6d853405fb49bc669cc53416f135864b5144d86c3405ee50154c57  boundary_note_arxiv.tar.gz (459,233 B)
    187110f5c840eb7fc0047b972a7950f7022d8a6478d0ccee41144bf5369d13e0  even_boundary_arxiv.tar.gz (451,300 B)

`anc/` here is byte-identical to the shared ancillary of those tarballs except two repository
localizations disclosed in `anc/README.md` (its own title/paths, and the manuscript lines of
`anc/SHA256SUMS` pointing to `paper/`).

Every release of this repository is archived on Zenodo. Cite the concept DOI
[10.5281/zenodo.21670577](https://doi.org/10.5281/zenodo.21670577), which always resolves to the
latest version; both papers cite it in their data-availability statements.

## Provenance and disclosure

This work was carried out with substantial AI assistance in derivation, computation, and
drafting. The pair went through thirteen independent external referee reports, with findings tracked in
ledgers across nineteen review rounds for the note (among them a dedicated bibliography
verification — every external reference matched against MathSciNet/OpenAlex records) and nine
for the companion — every finding dispositioned, the two open items both being the same
user-gated step: inserting the note's arXiv identifier into the companion, which completes at
upload. Report #12, from a fresh reviewer,
requested a major revision while identifying no mathematical error; its requests (an explicit
Main Theorem, a novelty calibration, an appendix rewrite, visible checkpoint chains) were
applied in full. The final report #13: accept after minor revision — the referee recompiled the
manuscript, verified the manifest, and re-ran the whole battery. The companion's latest round
(minor revision / accept after mandatory corrections) turned two of its own findings into
machine checks rather than weakened wording: the twenty-four missing deep-closure routes were
computed and are now re-verified from the definitions by runner step 19 — which immediately
caught two hand-entered rows in the wrong format — and the build check, having missed sixteen
recoverable LaTeX errors behind a passing PDF, now greps for them directly. Every claim is backed by the proofs in the papers and the exact
certificates here; the author takes full responsibility for all proofs, code, and bibliographic
claims.

## License

MIT for the code and data in this repository (see `LICENSE`). The paper texts are © the author.
