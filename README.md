# Symbolic Execution is (Not Quite) All You Need

**Version 0.0.2**

## Abstract

Given a programming language implementation running on a host machine and a grammar, you can use symbolic execution and formal ISA semantics as oracles to extract a formal labeled transition system that simulates the implementation's behavior.

In plain terms: You can automatically derive executable formal specs from implementations — no one writes specs, everyone writes implementations, but you can't prove things about implementations directly. This technique lets you get the spec from the implementation (given its grammar).

## On working in public

I'm working on this solo, under difficult circumstances, with limited resources. I'm putting this out in an incomplete state because I've reached a point where I can't tell fast enough on my own whether the core idea is sound. If working in public helps me learn sooner that I need to rewrite the whole thing, all the better. Polishing will continue regardless — but fundamental course corrections benefit from early eyes.

## Feedback

**Important caveat**: The central claim may not be true. This paper is an attempt to find out. The title will adapt based on what reviewers and proofs verify. If there are limits, the goal is to delineate them.

**Background assumed**: You don't need a formal CS education (I'm a high school dropout), but you do need familiarity with some formal CS concepts — or strong mathematical proficiency. Reading the notation section carefully is advisable, though not strictly required if you're already familiar with the relevant niches. That said, multiple niches are at play and I don't inhabit any of them, so I don't know how well I matched their conventions. Evaluating the claims requires familiarity with LTSes, symbolic execution, formal methods, and some logic. I am not trying to explain this paper to non-programmers.

**What I'm looking for**:
- Is the main thrust true, useful, and worthwhile — or fundamentally flawed?
- Substantive technical objections ("this is impossible because X")
- Constructive feedback: how to make things clear, not just that they aren't
- Errors in statements or notation — prioritized to unblock main clarification work, not exhaustive
- Feedback on structure, scope, and meta-level concerns is also welcome

**What I'm not looking for**:
- "This draft isn't immediately publishable" (I know — but the skeleton of something publishable is there)
- Feedback that doesn't meet me halfway — please apply principle of charity

**How to submit feedback**: [GitHub issues](https://github.com/heartpunk/symex-is-not-quite-all-you-need/issues) preferred. [Bluesky](https://bsky.app/profile/heartpunk.bsky.social) replies also work.

**On references**: Please refer to a specific commit, file, and line number when commenting. Stable GitHub links are ideal. Substantial feedback without clear references may be ignored or sent back.

**On priorities**: My goal is improving the paper for version 1.0, not educating pre-1.0 readers. When those are in tension, I will prioritize 1.0 clarity. I will prioritize feedback that improves the paper and may ignore feedback that doesn't contribute to that goal.

**Please be kind and gentle.** I'm working on this solo and am quite invested. Disagreement is welcome if done nicely; viciousness is not tolerated.

## Files

- `paper/main.tex` / [main.pdf](paper/main.pdf) — where the final paper will end up
- `paper/scratch.tex` / [scratch.pdf](paper/scratch.pdf) — where the bulk of the current draft is (red text is LLM-derived, black text is human-written)
- `paper/refs.bib` — citations (incomplete; many papers yet to be added)
- `paper/template/` — IEEE LaTeX template files (class file, bibliography styles)
- `paper/watch.sh` — helper script for watching paper changes during drafting
- `lean/` — Lean 4 mechanization (0 sorry across all files)

## Repository State

1. `paper/scratch.tex` / `paper/scratch.pdf` are the most complete drafts.
2. Red text is LLM-derived. We intend to replace it fully before final submission, but it has all been reviewed to ensure it roughly reflects an important aspect of the system.
3. Sections were written at different points in time with different variants of the technique in mind; they have not yet been made fully consistent.
4. Many variants of aspects of the overall technique have been considered and may be reconsidered if something doesn't work, or for future extensions. Signs of inconsistency are likely related to this.
5. The most glaring issue: not everything is fully defined before use. Trying to fix this, but there's a lot to reorder.
6. The diagrams after the main text are experiments; not yet sure how to integrate them, but some need to be integrated.

## Target Venue

2026 LangSec Workshop (paper or work-in-progress report). If that doesn't work out, we'll adapt and submit elsewhere.

## Building

Requires LaTeX. One-off build: `cd paper && latexmk -pdf scratch.tex`

For continuous compilation with Skim auto-reload (macOS): `cd paper && ./watch.sh`

## Citation

See `CITATION.cff`, or use GitHub's "Cite this repository" button.

## License

Documentation: [CC-BY-SA-4.0](https://creativecommons.org/licenses/by-sa/4.0/)
Code: [GPL-3.0](https://www.gnu.org/licenses/gpl-3.0.html)

## Versioning

[SemVerDoc](https://semverdoc.org/), starting at 0.0.1.
