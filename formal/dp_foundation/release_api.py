"""Small Python-facing session using the generated, verified gate.

One sequential/session-scoped accountant; not a persistent service or a sandbox
against malicious Python in this process. Validation errors are ingestion errors,
not DP releases. Construct one session per protected dataset/accounting scope.
"""
from dataclasses import dataclass
from fractions import Fraction
from threading import Lock
from typing import Iterable

import _dafny
import FlatInput as FI
import GaussianGate as GG
import PrivacyCost as PC
from trusted_gaussian import prepare


@dataclass(frozen=True)
class ReleaseResult:
    accepted: bool
    values: tuple[Fraction, ...]
    spent: Fraction


class ReleaseError(RuntimeError):
    """The release failed; a reserved privacy charge is not refunded."""


def _positive_int(value: int, name: str) -> int:
    if type(value) is not int or value <= 0:
        raise ValueError(f"{name} must be a positive integer")
    return value


class ReleaseSession:
    def __init__(self, rows: Iterable[tuple[int, int, int]], *, cap: int,
                 a_card: int, b_card: int, budget: Fraction):
        if type(cap) is not int or cap < 0:
            raise ValueError("cap must be a nonnegative integer")
        _positive_int(a_card, "a_card")
        _positive_int(b_card, "b_card")
        if not isinstance(budget, Fraction) or budget < 0:
            raise ValueError("budget must be a nonnegative Fraction")
        snapshot = tuple(tuple(row) for row in rows)
        for row in snapshot:
            if (len(row) != 3 or any(type(x) is not int for x in row)
                    or row[0] < 0 or not 0 <= row[1] < a_card
                    or not 0 <= row[2] < b_card):
                raise ValueError("Input outside the declared ingestion domain")
        self._raw = _dafny.Seq([FI.RawRecord_RawRecord(*row) for row in snapshot])
        self._cap, self._a, self._b = cap, a_card, b_card
        self._budget = GG.default__.NewBudget(PC.Rat_Rat(budget.numerator, budget.denominator))
        self._lock = Lock()

    @property
    def spent(self) -> Fraction:
        with self._lock:
            value = self._budget.Used()
            return Fraction(value.num, value.den)

    def release(self, *, variance: Fraction) -> ReleaseResult:
        if not isinstance(variance, Fraction) or variance <= 0:
            raise ValueError("variance must be a positive Fraction")
        vn, vd = variance.numerator, variance.denominator
        # Check dependency and numeric support using PUBLIC information only.
        prepare(self._cap, vn, vd)
        with self._lock:
            request = GG.default__.CheckedBuild(self._raw, self._cap, self._a, self._b, vn, vd)
            if not request.is_Ready:
                raise ValueError("Input outside the declared ingestion domain")
            try:
                accepted, noisy = self._budget.Release(request.request)
            except Exception:
                # The generated gate already reserved the charge. Do not refund
                # or retry; do not expose backend errors that might contain input.
                raise ReleaseError("Release failed; reserved budget remains spent") from None
            used = self._budget.Used()
            return ReleaseResult(accepted, tuple(Fraction(x) for x in noisy),
                                 Fraction(used.num, used.den))
