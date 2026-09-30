# {{ problem_id }}

Prove every declaration left incomplete in `/app/Submission.lean`.

{{ title }}

The submission contains {{ hole_summary }}.

This is the source-free benchmark condition: no informal textbook excerpt is
bundled. Use the formal declarations in the workspace and Mathlib.

You may edit only:

- `/app/Submission.lean`
- Lean files under `/app/Submission/`

Do not modify `Challenge.lean`, `ChallengeDeps.lean`, `Solution.lean`, or the
workspace configuration. They are trusted benchmark files, and the verifier
replaces them with pristine copies before grading.

You may use Mathlib freely. Any helper code not already available in Mathlib
must be included under `/app/Submission/` and imported by `Submission.lean`.

The `lean-repl` and `loogle` tools are available for checking Lean snippets and
searching the pinned Mathlib version.

The final submission must type-check without `sorry`, `admit`, new axioms, or
other unproven gaps.
