# Manual revision comparison

This document records a three-way comparison of the original manual, the
Claude revision, and the independent ChatGPT revision.  The comparison should
judge each change against the original rather than treating either revision as
the default winner.

## Frozen comparison snapshots

The comparison worktrees are detached at the following commits.  They are
intended for inspection and rebuilding documentation, not for editing.

| Version | Commit | Local worktree | Rendered manual |
| --- | --- | --- | --- |
| Before revision | `b2435e9` | `/Users/highernash/Developer/SteinFactorizationM2-comparison/before` | [Open HTML manual](</Users/highernash/Developer/SteinFactorizationM2-comparison/before/doc-build/share/doc/Macaulay2/SteinFactorization/html/index.html>) |
| Claude revision | `91db3ea` | `/Users/highernash/Developer/SteinFactorizationM2-comparison/claude` | [Open HTML manual](</Users/highernash/Developer/SteinFactorizationM2-comparison/claude/doc-build/share/doc/Macaulay2/SteinFactorization/html/index.html>) |
| ChatGPT revision | `c1355b8` | `/Users/highernash/Developer/SteinFactorizationM2-comparison/chatgpt` | [Open HTML manual](</Users/highernash/Developer/SteinFactorizationM2-comparison/chatgpt/doc-build/share/doc/Macaulay2/SteinFactorization/html/index.html>) |

All three manuals were regenerated successfully with Macaulay2 1.26.06.  The
original version emitted only the pre-existing citation-metadata warning.

To rebuild one snapshot, run `make docs-all` in its worktree.  Because each
snapshot is detached at a fixed commit, later branch changes do not silently
alter this comparison.

## Comparison procedure

Use all three views below.  A direct Claude-versus-ChatGPT diff alone does not
show whether one revision unnecessarily changed sound original material.

1. Read the three rendered HTML pages side by side, beginning with the package
   overview and then following the functions in a normal user's workflow.
2. Inspect `b2435e9..91db3ea` to identify Claude's changes from the original.
3. Inspect `b2435e9..c1355b8` to identify ChatGPT's changes from the original.
4. Inspect `91db3ea..c1355b8` only after the first two comparisons, to isolate
   disagreements between the revisions.
5. Run equivalent examples and tests whenever a difference affects behavior,
   an accepted input, a return value, or a mathematical claim.

Useful commands from the main repository are:

```text
git diff b2435e9..91db3ea -- SteinFactorization.m2
git diff b2435e9..c1355b8 -- SteinFactorization.m2
git diff 91db3ea..c1355b8 -- SteinFactorization.m2
```

Use the same form with `README.md`, `IMPLEMENTATION.tex`, or `tests/` to narrow
the comparison.  `git diff --word-diff` is useful for prose-heavy passages.

## Decision labels

Give every substantive disagreement one of these labels:

- **Claude**: adopt Claude's version.
- **ChatGPT**: adopt ChatGPT's version.
- **Combine**: retain complementary parts of both revisions.
- **Original**: neither revision improves the original.
- **Rewrite**: all three versions need a new solution.
- **Defer**: a mathematical or compatibility decision is still required.

Do not decide by prose length alone.  Prefer the shortest explanation that is
mathematically correct, states the actual guarantee of the implementation, and
gives the reader enough information to use the function safely.

## Overall comparison

| Area | Original | Claude | ChatGPT | Preferred result | Reason |
| --- | --- | --- | --- | --- | --- |
| Mathematical accuracy |  |  |  |  |  |
| Package overview and workflow |  |  |  |  |  |
| Public API and naming |  |  |  |  |  |
| Return-value documentation |  |  |  |  |  |
| Preconditions and error messages |  |  |  |  |  |
| Examples |  |  |  |  |  |
| Readability and concision |  |  |  |  |  |
| Backward compatibility |  |  |  |  |  |
| Tests |  |  |  |  |  |
| README and implementation note |  |  |  |  |  |

## Detailed decisions

Copy the following block for each substantive difference.  Keep API changes,
mathematical corrections, and editorial changes as separate entries even when
they occur in the same paragraph.

### C-001: Short description

- **Location:** function or document section
- **Category:** correctness / API / validation / example / exposition / test
- **Original:** summary of the original behavior or wording
- **Claude:** summary of Claude's change and stated rationale
- **ChatGPT:** summary of ChatGPT's change and rationale
- **Evidence:** rendered output, source lines, test result, or mathematical fact
- **Decision:** Claude / ChatGPT / Combine / Original / Rewrite / Defer
- **Reason:** why this choice best serves users
- **Final action:** exact change needed in the eventual integration branch

## Questions requiring special attention

The following topics can change package behavior or user expectations and
should not be settled as ordinary copy editing.

- Does each use of “certified” name exactly the property that is checked?
- Should `checkChartwiseInverses` be public, private, or removed?
- Which return-table keys constitute supported public API?
- Is the one-argument form of `steinCoordinateAlgebra` preferable, and should
  the two-argument form remain for compatibility?
- Which validation failures should produce explicit errors?
- Do the weighted-projective and twisted-cubic examples state the correct
  grading, morphism, image, and degree?
- Which names are mathematical conventions worth retaining, even if short?
- Are implementation details being presented as mathematical guarantees?

## Final integration checklist

- [ ] Every entry in the detailed decision log has a disposition.
- [ ] Mathematical claims have been checked independently of prose quality.
- [ ] Public names, signatures, return keys, examples, and tests agree.
- [ ] The package overview describes one coherent user workflow.
- [ ] All documentation examples run without errors.
- [ ] Standard, weighted, and twisted-cubic tests pass.
- [ ] README and `IMPLEMENTATION.tex` match the final implementation.
- [ ] The final HTML manual has been read in rendered form.
- [ ] Breaking changes and compatibility decisions are recorded explicitly.
