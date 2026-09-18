"""Demonstration backend only, not a verified or production DP sampler.

The formal claim assumes a backend with the declared Gaussian law and fresh
randomness. This floating-point adapter exercises the FFI and is NOT evidence
that Python's normal sampler satisfies that probabilistic contract.
"""
from math import sqrt
from random import SystemRandom
import _dafny

_rng = SystemRandom()

class default__:
    @staticmethod
    def Sample(center, varianceNum, varianceDen):
        sigma = sqrt(varianceNum / varianceDen)
        # Keep the integer mean exact when adding the sampled finite float.
        return _dafny.Seq([
            _dafny.BigRational(n) + _dafny.BigRational(_rng.gauss(0.0, sigma))
            for n in center
        ])
