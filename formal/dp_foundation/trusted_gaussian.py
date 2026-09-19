"""Trusted OpenDP 0.15.1 discrete-Gaussian adapter, NOT proved by Dafny.

Only public parameters are used in calibration. The exact rational charge in
Dafny must dominate OpenDP's upward-rounded privacy map. Integer centers are
saturated by the VERIFIED caller before entering the i64 backend; conversion to
float is never applied to private counts. There is no demonstration fallback.
"""
from dataclasses import dataclass
from fractions import Fraction
from functools import lru_cache
from importlib.metadata import version
import math
from typing import Any

import opendp.prelude as dp
import _dafny

if version("opendp") != "0.15.1":
    raise RuntimeError("This adapter is reviewed and tested only with OpenDP 0.15.1")
dp.enable_features("contrib")


@dataclass(frozen=True)
class Calibration:
    scale: float
    sensitivity: float
    charge: Fraction
    backend_bound: Fraction
    measurement: Any


@lru_cache(maxsize=128)
def prepare(cap: int, variance_num: int, variance_den: int) -> Calibration:
    """Construct a PUBLIC calibration receipt, or reject unsupported parameters.

    The receipt is inspectable evidence, not a new sampler proof. OpenDP's
    privacy map and randomness implementation remain trusted.
    """
    if any(type(x) is not int for x in (cap, variance_num, variance_den)):
        raise TypeError("Calibration parameters must be integers")
    if cap < 0 or variance_num <= 0 or variance_den <= 0:
        raise ValueError("Invalid public Gaussian parameters")
    variance = Fraction(variance_num, variance_den)
    charge = Fraction(cap * cap * variance_den, 2 * variance_num)
    try:
        sensitivity = float(cap)
        scale = math.sqrt(float(variance))
    except (OverflowError, ValueError) as exc:
        raise ValueError("Public parameters exceed supported floating-point range") from exc
    if not (math.isfinite(sensitivity) and math.isfinite(scale) and scale > 0):
        raise ValueError("Public parameters exceed supported floating-point range")
    if Fraction.from_float(sensitivity) < cap:
        sensitivity = math.nextafter(sensitivity, math.inf)
    if not math.isfinite(sensitivity):
        raise ValueError("Public sensitivity exceeds supported range")

    for _ in range(32):
        # Exact check of the floating-point scale's rational value.
        if Fraction.from_float(scale) ** 2 < variance:
            scale = math.nextafter(scale, math.inf)
            continue
        mechanism = dp.m.make_gaussian(
            dp.vector_domain(dp.atom_domain(T="i64")),
            dp.l2_distance(T=float),
            scale=scale,
        )
        rho = mechanism.map(sensitivity)
        if not math.isfinite(rho) or rho < 0:
            raise ValueError("Unsupported public privacy-map result")
        backend_bound = Fraction.from_float(rho)
        if backend_bound <= charge:
            return Calibration(scale, sensitivity, charge, backend_bound, mechanism)
        scale = math.nextafter(scale, math.inf)
        if not math.isfinite(scale):
            break
    raise ValueError("Cannot conservatively calibrate these public parameters")


class default__:
    @staticmethod
    def Sample(center, cap, varianceNum, varianceDen):
        plan = prepare(cap, varianceNum, varianceDen)
        # Caller proves 0 <= each count <= i64::MAX. OpenDP handles the noise
        # and finite-range output internally. Do NOT add bounded noise manually.
        noisy = plan.measurement(list(center))
        return _dafny.Seq([_dafny.BigRational(n) for n in noisy])
