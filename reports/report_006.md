# Report T05 — Switch to LNCS formatting + T12 CITATION.cff

## What was done

### paper/main.tex

1. **Document class**: `article` → `llncs`
2. **Removed packages**: `geometry` (LNCS handles margins), `todonotes` (no longer
   needed; `\comment{}` now silenced via `\newcommand{\comment}[1]{}`)
3. **Removed**: `\geometry{...}` line, `\date{}`, `\amsthm` (not in llncs)
4. **Author block**: replaced placeholder with LNCS `\author` + `\institute`:
   - Silvère Gangloff — IT4Innovations / IRAFM, University of Ostrava
   - Jan Hula — same affiliation
   - Miroslav Olšák — CIIRC, Czech Technical University in Prague
5. **Keywords**: added `\keywords{...}` after abstract (required by LNCS)
6. **Bibliography style**: `plain` → `splncs04` (required for LNCS/Springer)

### CITATION.cff

Created `CITATION.cff` at repo root with all three authors, affiliations, emails,
and the GitHub repository URL.

## Why

ITP uses Springer LNCS format. The `llncs` class enforces correct margins,
font sizes, and header styles; using `article` would require manual adjustment
and would not match the final proceedings layout. Switching now lets us see the
real page count and cut material if over 8 pages.
