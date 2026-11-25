# Research notes: tasks 1904 and 2071

## STATUS

These notes share local experiments for the
pequalnp project. They do not solve L-meta-1904 or L-meta-2071 and do not claim
new mathematical theorems or official project credit.

## WHAT MAY BE USEFUL TO OTHER RESEARCHERS

1. Exact SAT encodings, independently checked positive circuits, graph edge
   lists, and recorded search limits. These can prevent repetition of precisely
   the same bounded experiments; they do not rule out further search.
2. Smaller encodings using monotonicity and the first-unsafe-AND criterion
   already proved inside upstream R_meta_1904_493 (PR 6844). The criterion itself
   is existing work and is not claimed here as a new contribution.
3. Lean diagnostics checking concrete reference circuits, legality, and traces.
   These diagnostics do not establish the minimality required by either task.

## RESULTS AND LIMITS

1904: two eight-vertex subgraphs of Petersen, with clean reference circuits of
13 and 12 gates. Positive SAT models were checked against every clause and all
256 inputs. Separate Lean diagnostics check reference constructions, short-cycle
exclusion, exact outputs and cleanliness. Smaller-circuit searches returned
UNKNOWN after 2,000,000 conflicts, with both full and small-row encodings.

2071: a local block consisting of two degree-four stars sharing one line, with
nine inputs and nine gates. Positive models were checked on all 512 inputs.
The 49-row encoding includes every input of size at most two and all four maximal
independent inputs. Double-read searches returned UNKNOWN after 1,000,000
conflicts in both encodings. This is a local block, not a 64-gate plane search.

An additional 67-gate diagnostic checks syntax, a dirty unused AND, positive
andPairs, two false scalar traces and a two-variable gadget identity in Lean.
Its full plane-function equality was NOT kernel-certified: that symbolic
attempt was stopped as too costly. The unverified attempt is not included here.
The diagnostic exceeds the task's 64-gate bound and is NOT a counterexample.

UNKNOWN is not UNSAT, not an exhaustion certificate, and not a lower bound.
All successful included Lean diagnostics used only propext, Classical.choice,
and Quot.sound (some used fewer). They are local checks, not official acceptance
of a new contribution. Reference constructions largely reproduce known cases.

## REPRODUCTION

Recorded tools: Node.js 18.20.3, CaDiCaL 2.1.2, Lean 4.36.0.
Set CADICAL to the path of your solver, or put cadical on PATH.
Run commands from this bundle's directory. Solver runs write CNF, log and JSON
files there; archived observations are separately kept in results/.

```sh
node src/research-1904-sat.cjs p8adj 13 clean
node src/research-1904-sat.cjs p8adj 12
node src/research-1904-pair.cjs p8adj 12 clean
node src/research-2071-stars.cjs 9 double 1000000
node src/research-2071-boundary.cjs 9 double 1000000
node src/research-2071-local.cjs 3
```

The files in `results/` are archived observations. Scripts write fresh outputs to the current working directory.

1904 scripts have a fixed 2,000,000-conflict limit. The 2071 local-star scripts
accept a conflict limit as their third numeric/positional argument, as shown.
Seeds, platforms and solver versions can change timings and whether a limited
run finds a model. No time estimate or guaranteed result is implied.

For Lean, use the project's pinned toolchain and dependencies. The local Defs
snapshot was the public fork commit 35f4cb7d2cbbe0cf88e7002b98c4e88515d01493.
From the repository's lean directory, run lake env lean on each included Lean
file by its absolute path. No file from this bundle has been submitted upstream.

## PROVENANCE

Public project: https://github.com/open-goat/pequalnp-proofs
Existing small-input criterion: https://github.com/open-goat/pequalnp-proofs/pull/6844
Public fork snapshot: https://github.com/Harchy33/pequalnp-proofs/tree/35f4cb7d2cbbe0cf88e7002b98c4e88515d01493
Participation rules: https://pequalnp.com/join.txt

Source programs and local diagnostics were prepared for Harchy33 with Codex.
The project definitions and cited upstream proofs retain their own authorship.
Only solver-path portability was changed when packaging the research scripts.
The manifest records original source hashes and packaged file hashes.
No credentials, lease identifiers, machine logs or executables are included.

Research branch: [research-notes-1904-2071](https://github.com/Harchy33/pequalnp-proofs/tree/research-notes-1904-2071/research/2026-11-25-1904-2071).
