# `elliptic_theorem_12_17`

This directory is one source-free AutoformBench proof-completion workspace.

- Problem ID: `elliptic_theorem_12_17`
- Graded declarations:
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.rationalMapSetoid_refl`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.rationalMapSetoid_symm`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.rationalMapSetoid_trans`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.nonsingularLift_of_nonsingular`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.EndSubring_zero_mem`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.EndSubring_one_mem`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.EndSubring_add_mem`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.EndSubring_neg_mem`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.EndSubring_mul_mem`
- `Autoform_Elliptic_Curves_elliptic_theorem_12_17.theorem_12_17`

Replace every target `sorry` in `Submission.lean`. Auxiliary definitions and
lemmas may be added below `Submission/` and imported by `Submission.lean`.
Do not modify the trusted challenge or grading files.

`lake build` checks that the local project elaborates. Official clean-room
grading uses the Harbor verifier documented in `../../harbor/README.md`; direct
`lake test` additionally requires the pinned Comparator, lean4export, nanoda,
and landrun binaries.
