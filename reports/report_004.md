# Report T04 — Writing polish: abstract and key claim

## What was done

### Abstract (paper/main.tex)

Rewrote the abstract to be tighter and more concrete (~150 words, within LNCS limit):
- Lead with the sharpest finding (LSP > planning alone) rather than the methodology
- Include concrete numbers from the quantitative table (17 tests, 307 LOC, 9 milestones)
- Name all four error classes that LSP uniquely fixes
- Remove the vague "discuss implications" sentence

### Introduction (paper/main.tex)

Added one sentence immediately after the four findings to make the key claim explicit:
> "The sharpest result is that LSP access to the live compiler is more valuable
> than planning alone: Condition C (no plan, LSP) strictly dominates Condition B
> (plan, no LSP) on every metric."

This addresses the open suggestion in suggestions.md §8 to make the main takeaway
explicit and early.

## Why

The previous abstract buried the key finding in the middle and didn't include
concrete numbers. The intro stated all four findings but did not single out the
most surprising one (C > B). Both changes make the paper's contribution immediately
clear to a reviewer reading the first page.
