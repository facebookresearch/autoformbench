# `elliptic_eichlerShimuraCarayol`

This directory is one source-free AutoformBench proof-completion workspace.

- Problem ID: `elliptic_eichlerShimuraCarayol`
- Graded declarations:
- `Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol.exists_gamma0FundamentalRegion`
- `Autoform_Elliptic_Curves_elliptic_eichlerShimuraCarayol.eichlerShimuraCarayol`

Replace every target `sorry` in `Submission.lean`. Auxiliary definitions and
lemmas may be added below `Submission/` and imported by `Submission.lean`.
Do not modify the trusted challenge or grading files.

`lake build` checks that the local project elaborates. Official clean-room
grading uses the Harbor verifier documented in `../../harbor/README.md`; direct
`lake test` additionally requires the pinned Comparator, lean4export, nanoda,
and landrun binaries.
