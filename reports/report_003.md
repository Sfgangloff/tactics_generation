# Report T03 — Condense pilot section

## What was done

Condensed the pilot section (`§3 Pilot: Intuitionistic Implication Tactic`) in
`paper/main.tex` from ~60 lines to ~20 lines (~1 page → ~half a page in LNCS).

The three-approach structure is preserved but now in compact numbered form rather
than full `\paragraph{}` blocks. The Julia/Catalan/Bell detail is reduced to one
sentence. The key insight ("model is a good code generator, poor mathematician")
and the pointer to the repo for full logs are kept.

## What was removed

- Detailed description of the characteristic failure in Approach 1 (the
  `((A → B → B) → C) → C` example)
- The displayed math formula for Approach 3 (kept inline)
- The "Outcome and caveats" paragraph (merged into a single closing sentence)
- The `\comment{}` annotation asking whether the section was too detailed

## Why

An ITP short paper is 8 pages in LNCS format. The main contribution is the 2×2
study; the pilot is motivating material. ~half a page is appropriate. All
the detail remains in `experiments/intuitionistic_pilot/README.md` and the
repo for readers who want it.
