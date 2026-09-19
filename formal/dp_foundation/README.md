# Dafny user-level marginal with an OpenDP release backend

Pinned tools: **Dafny 4.11.0**, **OpenDP 0.15.1**, Python 3.10 or newer.
Install the backend and run from the repository root:

```bash
python3 -m pip install -r formal/dp_foundation/requirements-backend.txt
bash formal/dp_foundation/run.sh
```

Set `DAFNY` to the executable path when necessary. This builds real Python from
Dafny; generated Python is not an independently handwritten approximation.

## What this revision adds

`VerifiedClient.dfy` closes the earlier external-client timeout example. Explicit
pre-call snapshots and assertion isolation allow the client to prove, using only
exported contracts, that a first release succeeds, a second exceeds the budget,
and the rejected call leaves the spent amount unchanged. No privacy or budget
postcondition was removed to get this proof through.

`NumericBoundary.dfy` proves coordinate saturation into the nonnegative i64
range does not increase the added-user squared L2 distance. The compiled gate
uses that same verified saturation function before calling the backend. It is
the identity for ordinary histogram counts; it prevents a private-count cast to
float or an out-of-range integer conversion at the library boundary.

`trusted_gaussian.py` now calls OpenDP's integer-vector discrete Gaussian, not
Python `random.gauss`. Its noise law differs from ideal continuous Gaussian
noise. The trusted OpenDP privacy map supplies the zCDP bound; the sampler and
its theorem are not re-proved here. OpenDP's `contrib` feature is required.

The API field `variance` denotes nominal sigma-squared, not the exact variance
of the integer-supported distribution. For public requested sigma-squared vn/vd and cap C, Dafny charges the exact rational
`C*C*vd/(2*vn)`. The adapter rounds the float sensitivity upwards and increases
the scale as needed. It accepts only when the exact rational representation of
OpenDP's reported privacy bound is at most that exact charge. Thus simply
rounding a nominal standard deviation down cannot silently reduce the noise.
These adapter checks are TESTED trusted Python, not Dafny proofs.

`release_api.py` keeps one dataset snapshot and generated budget in one session.
Its release result contains only the noisy vector and spent budget. A lock
serializes calls through this wrapper. An exception after reservation does not
refund the charge and is exposed as a generic failure. Rejection due to budget
exhaustion does not invoke the sampler.

## Results and reproducible evidence

The positive entry point checks **211 verified targets, 0 errors**, including
all imported files. The total includes assertion-isolated client obligations;
it is not a count of independent DP theorems. The core without the client has
141 verified targets. The audit lists one explicit external sampler assumption.

Tests retain the previous 341 grouping cases, 1,364 exhaustive histograms,
4,092 whole-UID deletion checks, 300 random histograms, 10 invalid input cases,
and a 3,000-row execution. Eleven new backend/session tests include 305 public
calibrations, 32 real repeated releases, exact 8/9 accounting, integer-boundary
handling, zero-cap behavior, failed-sampler accounting, and two concurrent calls
through one wrapper. The solver rejects seven bad proof/access-control fixtures.

### Important known contract gap

`probe_contract_scope.py` also records a different, deliberately nonprivate
mutation: replacing the sampler call with the raw saturated histogram. Dafny
**accepts** this mutation because the exported contract specifies shape and
accounting but not output provenance or information flow. The mutated program
is verified as a diagnostic, never run or imported by the active interface.
For an empty table versus one added UID, its first output cell is deterministically
0 versus 1, so the mutation does not satisfy any finite-epsilon DP claim with
delta below 1. This is a specification gap, not a Dafny soundness bug.

Accordingly, this is a working conditional-privacy implementation with verified
preprocessing, sensitivity bounds, range conversion and accounting. It is NOT
a machine-checked end-to-end DP theorem, and seven rejected mutations must not
be reported as detection of every privacy violation. The current release path
must remain reviewed/fixed trusted code until its output-flow contract is added.
The scope probe is preserved in CI to prevent that limitation from being lost.

## Python use

After running the build, put `formal/dp_foundation` and its generated
`artifacts/flat_pipeline-py` directory on `PYTHONPATH`:

```python
from fractions import Fraction
from release_api import ReleaseSession

session = ReleaseSession(
    [(7, 0, 1), (8, 1, 0), (7, 0, 1), (8, 0, 0), (7, 1, 1)],
    cap=2, a_card=2, b_card=2, budget=Fraction(3, 4),
)
first = session.release(variance=Fraction(4))
second = session.release(variance=Fraction(4))
assert first.accepted and first.spent == Fraction(1, 2)
assert not second.accepted and second.values == ()
```

## Scope that has not changed

Schema, cap, variance and budget are public. The privacy unit is a UID, removed
from arbitrary positions while preserving others' relative order. Input checking
is trusted ingestion: its data-dependent error messages are not DP outputs.
Dafny access control is not a sandbox for adversarial Python introspection.
Creating a fresh session resets its accountant; persistent dataset identity,
cross-session composition and process recovery are not implemented. The wrapper
lock does not prove concurrency correctness of direct generated-code calls.
Private marginal selection, full adaptive AIM, and utility/performance studies
remain outside this pilot. The interpreter, compiler, runtime, SMT solver,
OpenDP and the handwritten adapter/wrapper are explicit trust dependencies.

Primary backend documentation:
https://docs.opendp.org/en/v0.15.1/api/user-guide/measurements/additive-noise-mechanisms.html
https://docs.opendp.org/en/v0.15.1/api/python/opendp.measurements.html
