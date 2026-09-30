# AutoformBench for Harbor

This directory contains a source-free Harbor adapter for the audited public
AutoformBench release in `workspaces/`. The 241 workspaces are the
canonical benchmark representation; `tasks/` is generated from them by
`export.py` and must not be edited by hand.

The adapter targets **Harbor 0.22.0** and task schema **1.4**. Run every command
below from the repository root.

## Export the tasks

```bash
python3 harbor/export.py --all
python3 harbor/export.py --check
```

The exported task environments contain the formal Lean workspace only. They do
not contain textbook excerpts, private evaluation traces, accepted submissions,
or gold proofs. In particular, each workspace's `Solution.lean` is a generated
Comparator adapter that delegates the graded declarations to
`Submission.lean`; it is not a reference solution.

`tasks/` is a deterministic generated directory and is intentionally ignored by
Git. Regenerate it with `export.py --all`; validate it against the canonical
manifest and workspaces with `export.py --check`.

## Build the images

The image tags below are also the defaults used by the generated task
Dockerfiles:

```bash
docker build \
  -f harbor/images/agent/Dockerfile \
  -t autoformbench-agent:lean4.32.2-mathlib-905b9581 \
  .

docker build \
  --build-arg AGENT_IMAGE=autoformbench-agent:lean4.32.2-mathlib-905b9581 \
  -f harbor/images/verifier/Dockerfile \
  -t autoformbench-verifier:lean4.32.2-mathlib-905b9581 \
  .
```

Image construction needs network access to fetch the pinned Lean dependencies
and verifier sources. Task execution and verification are configured with no
network access.

The agent image contains Lean 4.32.2, Mathlib at commit
`905b95818eb32af7874a58b427f50c1711a5e96c`, and the Lean REPL and Loogle MCP
servers. The verifier additionally pins:

- Comparator: `789279735fe44c1c05dc54bb9f46ba4d9b8c7611`
- lean4export: `4e7915201d3f9f04470d9eae002fa695f7cdc589`
- nanoda: `68d5ca9db226849b41a6fff59d796ff19d0a8840`
- landrun: `5ed4a3db3a4ad930d577215c6b9abaa19df7f99f`

For a published evaluation, publish these images to an OCI registry and pin
their digests instead of relying on mutable local tags.

## Validate and run

Install or invoke the exact supported Harbor release:

```bash
HARBOR_TELEMETRY=0 uvx --from harbor==0.22.0 harbor --help
python3 harbor/export.py --check
```

Harbor enables anonymous usage telemetry by default. Setting
`HARBOR_TELEMETRY=0`, as in every runner command below, disables it. After the
pinned Harbor package has been installed once, add `UV_OFFLINE=1` and pass
`--offline` to `uvx` if the orchestration process itself must make no network
requests. Task execution and verification remain network-disabled either way.

Run the pristine expected-zero baseline over the generated collection:

```bash
HARBOR_TELEMETRY=0 uvx --from harbor==0.22.0 harbor run \
  -c harbor/jobs/all.yaml
```

To run one task with another Harbor agent, point Harbor at its generated task
directory and choose the agent and model supported by your installation:

```bash
HARBOR_TELEMETRY=0 uvx --from harbor==0.22.0 harbor run \
  -p harbor/tasks/<problem_id> \
  --agent <agent> \
  --model <provider/model>
```

For a fully local smoke test after Harbor and the two images are available:

```bash
HARBOR_TELEMETRY=0 UV_OFFLINE=1 \
uvx --offline --from harbor==0.22.0 harbor run \
  -p harbor/tasks/alg_top_theorem107 \
  --agent nop \
  --n-attempts 1 \
  --n-concurrent 1
```

This expected-zero test should complete without an infrastructure exception and
report reward `0`: the `nop` agent leaves the seeded `sorry` untouched, which
the verifier must reject. On Linux, Harbor's isolated Docker bridge requires
IPv4 forwarding to be enabled on the Docker host.

The default job uses Harbor's `nop` agent deliberately. Every pristine
submission still contains at least one `sorry`, so a correct verifier should
assign reward 0 to every task.

## Trust boundary and grading

The agent can edit `/app/Submission.lean` and Lean files below
`/app/Submission/`. Harbor transfers only those artifacts to a separate,
offline verifier environment. The verifier does not trust any other file from
the agent container. It:

1. validates the submitted artifact and rejects links or non-Lean helpers;
2. copies the corresponding canonical workspace from the read-only release
   snapshot into a fresh temporary directory;
3. overlays only `Submission.lean` and `Submission/`;
4. enables the independent nanoda kernel check; and
5. runs Comparator to check target equality, permitted axioms, Lean kernel
   acceptance, and nanoda replay.

Verifier infrastructure errors are reported separately from rejected
submissions and do not receive a numerical reward. The verifier image contains
all canonical challenge workspaces because those are trusted grading inputs;
the agent image receives only the selected source-free workspace.
