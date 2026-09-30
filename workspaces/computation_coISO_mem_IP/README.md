# `computation_coISO_mem_IP`

This directory is one source-free AutoformBench proof-completion workspace.

- Problem ID: `computation_coISO_mem_IP`
- Graded declarations:
- `coISO_mem_IP`

Replace every target `sorry` in `Submission.lean`. Auxiliary definitions and
lemmas may be added below `Submission/` and imported by `Submission.lean`.
Do not modify the trusted challenge or grading files.

`lake build` checks that the local project elaborates. Official clean-room
grading uses the Harbor verifier documented in `../../harbor/README.md`; direct
`lake test` additionally requires the pinned Comparator, lean4export, nanoda,
and landrun binaries.
