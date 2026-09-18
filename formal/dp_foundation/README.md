# Verified flat-record user-level marginal pipeline

This extends the earlier `FoundationPilot.dfy`. The supported input is an ordered
flat table of `(uid, a, b)` records, not pre-grouped user blocks.

Run with **Dafny 4.11.0** and Python 3:

```bash
bash formal/dp_foundation/run.sh
```

From this directory, `bash run.sh` is equivalent. Set `DAFNY` when the executable
is not on PATH. No third-party Python packages are needed.

## What is verified

`GaussianGate.dfy` includes `FlatGrouping.dfy` and `FoundationPilot.dfy`.
The verification command uses `--verify-included-files`: all three are checked.
The current positive run reports **130 verified, 0 errors**.

* Stable grouping produces one block per UID and exactly that UID's records in
  their original relative order. Noncontiguous occurrences share one cap.
* The mutable histogram implementation agrees with the SAME shared histogram
  specification used by the sensitivity theorem.
* Removing all occurrences of one UID from arbitrary positions leaves the other
  users' bounded contributions unchanged. The delta has L1 norm at most `cap`
  and squared L2 norm at most `cap * cap`.
* The Gaussian request constructor is hidden from Dafny clients. Its verified
  factory ties the exact center to this query family and computes
  `rho = cap^2 * varianceDen / (2 * varianceNum)`.
* Exact-rational arithmetic is related to its real-valued meaning by checked
  lemmas. A stateful budget object reserves the exact charge BEFORE calling the
  backend. Its limit is unchanged and its used budget cannot exceed that limit.
* Signed raw records and public numeric parameters have compiled validation.
  The checked factory accepts exactly the inputs satisfying its stated domain.

The executable grouping and marginal path uses loops. Recursive mathematical
functions and proof lemmas are not called on the large-input execution path.
This is still a correctness prototype, not an optimized grouping library.

## Evidence

`run.sh` writes the verifier, translator, audit, runtime and negative-check logs
under `artifacts/`. Locally, Python 3.13.5 passed 341 grouping cases, 1,364
exhaustive histograms, 4,092 whole-UID deletion checks, 300 randomized histograms,
10 invalid-input checks, and a 3,000-record execution check.

The accept-then-reject test uses cap=2, variance=4, and total rho=3/4. The first
release spends 1/2; the second is rejected. The backend is called exactly once.
An injected backend exception leaves the reserved charge spent.

Six negative cases must be rejected: bypass clipping, omit the charge,
underestimate sensitivity, forge a request, access the hidden backend, and reset
private budget fields. Positive verification checks every included source;
mutation tests recheck the affected obligation, while access-control tests fail
at name/type resolution. Timeouts are NOT counted as successful detection.

## Trust and scope

The audit lists exactly one explicit external assumption:
`GaussianGate.GaussianBackend.Sample`. Its Dafny contract checks output shape.
The Gaussian distribution, fresh randomness, lack of extra output, and the
Gaussian/zCDP composition theorems remain TRUSTED mathematical/backend
assumptions. No probabilistic semantics or complete AIM privacy theorem is
proved in these files.

`trusted_gaussian.py` is a demonstration adapter using Python floating-point
normal sampling. It is NOT a certified or production DP sampler. Executing it
checks the integration only. A production backend must satisfy the assumed law
and numeric contract; it cannot be made certified merely by implementing the
same Python method name.

Opaque constructors and private fields are enforced for verified DAFNY callers.
Generated Python does not enforce those proof restrictions against arbitrary
Python code. The Python interpreter, Dafny compiler/runtime, and any handwritten
wrapper remain trusted. One budget session must be maintained for a dataset;
creating multiple new sessions is not prevented by this prototype.

The privacy unit is a UID. The proved adjacency removes all its records while
preserving the other records' relative order. Schema, cap, variance, and budget
are public parameters. Invalid-data error flags are not covered by the privacy
claim across valid/invalid inputs. Validation belongs at a trusted ingestion
boundary, or requires a separately specified privacy-preserving error policy.
Private marginal selection, full adaptive AIM, persistence and concurrency are
outside this experiment.

## Explicitly unfinished experiment

`experiments/ClientAcceptanceUnknown.dfy` attempts a stronger external-client
proof: for all valid raw tables, one call succeeds and the next fails under the
concrete budget above, using only exported contracts. It encountered solver
timeouts and is marked **UNKNOWN**. It is not part of the 130-verified claim and
is not included by the active entry point. The same behavior passed execution
checks; those checks are not substituted for this missing proof.

```bash
dafny verify experiments/ClientAcceptanceUnknown.dfy \
  --filter-symbol=VerifiedClient --verification-time-limit 15
```

Next work: resolve this cross-module proof/abstraction issue, add a minimal
verified public client, and then connect a reviewed sampler backend. Do not
expand to full AIM before that interface is stable.
