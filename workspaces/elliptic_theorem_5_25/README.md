# `elliptic_theorem_5_25`

This directory is one source-free AutoformBench proof-completion workspace.

- Problem ID: `elliptic_theorem_5_25`
- Graded declarations:
- `Autoform_Elliptic_Curves_elliptic_theorem_5_25.mulByXCoord_denominator_ne_zero`
- `Autoform_Elliptic_Curves_elliptic_theorem_5_25.mulByXCoord_numerator_coprime_denominator`
- `Autoform_Elliptic_Curves_elliptic_theorem_5_25.theorem_5_25`

Replace every target `sorry` in `Submission.lean`. Auxiliary definitions and
lemmas may be added below `Submission/` and imported by `Submission.lean`.
Do not modify the trusted challenge or grading files.

`lake build` checks that the local project elaborates. Official clean-room
grading uses the Harbor verifier documented in `../../harbor/README.md`; direct
`lake test` additionally requires the pinned Comparator, lean4export, nanoda,
and landrun binaries.
