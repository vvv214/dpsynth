"""Runtime integration evidence; no statistical tests are treated as DP proofs."""
from concurrent.futures import ThreadPoolExecutor
from fractions import Fraction
from importlib.metadata import version
import json
import math
from pathlib import Path
import random
import sys
import unittest
from unittest.mock import patch

ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT / "artifacts" / "flat_pipeline-py"))
sys.path.insert(0, str(ROOT))
import _dafny
import NumericBoundary as NB
import trusted_gaussian as backend
from release_api import ReleaseError, ReleaseSession

ROWS = [(7,0,1),(8,1,0),(7,0,1),(8,0,0),(7,1,1)]
OBSERVATIONS = {"opendp_version": version("opendp"), "calibrations": 0}


def session(budget=Fraction(3,4), cap=2):
    return ReleaseSession(ROWS, cap=cap, a_card=2, b_card=2, budget=budget)


class BackendTests(unittest.TestCase):
    def test_public_calibration(self):
        rng = random.Random(49281)
        examples = [(2,4,1),(2,9,4),(3,2,1),(0,4,1),(2**53+1,10**30,1)]
        examples += [(rng.randrange(0,1000),rng.randrange(1,100000),rng.randrange(1,100000))
                     for _ in range(300)]
        for cap,vn,vd in examples:
            plan = backend.prepare(cap,vn,vd)
            self.assertGreaterEqual(Fraction(plan.scale)**2, Fraction(vn,vd))
            self.assertGreaterEqual(Fraction(plan.sensitivity),cap)
            self.assertEqual(plan.charge,Fraction(cap*cap*vd,2*vn))
            self.assertLessEqual(plan.backend_bound,plan.charge)
            OBSERVATIONS["calibrations"] += 1
        example=backend.prepare(2,9,4)
        OBSERVATIONS["non_dyadic_receipt"]={
            "variance":"9/4", "charge":str(example.charge),
            "scale":example.scale, "backend_bound":str(example.backend_bound)}

    def test_real_accept_then_reject(self):
        s=session()
        with patch.object(backend.default__,"Sample",wraps=backend.default__.Sample) as call:
            a=s.release(variance=Fraction(4))
            b=s.release(variance=Fraction(4))
        self.assertTrue(a.accepted)
        self.assertEqual(len(a.values),4)
        self.assertEqual(a.spent,Fraction(1,2))
        self.assertFalse(b.accepted)
        self.assertEqual(b.values,())
        self.assertEqual(b.spent,Fraction(1,2))
        self.assertEqual(call.call_count,1)
        self.assertFalse(hasattr(a,"center"))
        self.assertFalse(hasattr(a,"request"))
        OBSERVATIONS["real_example_output"]=[str(x) for x in a.values]
        OBSERVATIONS["denied_backend_calls"]=0

    def test_no_refund_on_failure(self):
        s=session()
        with patch.object(backend.default__,"Sample",side_effect=RuntimeError("private detail")):
            with self.assertRaisesRegex(ReleaseError,"reserved budget remains spent") as e:
                s.release(variance=Fraction(4))
        self.assertNotIn("private detail",str(e.exception))
        self.assertEqual(s.spent,Fraction(1,2))
        self.assertFalse(s.release(variance=Fraction(4)).accepted)

    def test_zero_cap_zero_charge(self):
        s=session(budget=Fraction(0),cap=0)
        r=s.release(variance=Fraction(4))
        self.assertTrue(r.accepted)
        self.assertEqual(r.spent,Fraction(0))
        self.assertEqual(len(r.values),4)

    def test_integer_range_bridge(self):
        maximum=9223372036854775807
        values=[0,1,maximum,maximum+1,10**100]
        clipped=NB.default__.Saturate(_dafny.Seq(values))
        self.assertEqual(list(clipped),[0,1,maximum,maximum,maximum])
        noisy=backend.default__.Sample(clipped,2,4,1)
        self.assertEqual(len(noisy),5)
        self.assertTrue(all(-2**63<=x<=maximum for x in noisy))

    def test_saturation_does_not_increase_distance(self):
        rng=random.Random(74)
        ceiling=9223372036854775807
        for _ in range(100):
            base=[rng.randrange(ceiling-10,ceiling+10) for _ in range(5)]
            delta=[rng.randrange(0,5) for _ in range(5)]
            a=list(NB.default__.Saturate(_dafny.Seq(base)))
            b=list(NB.default__.Saturate(_dafny.Seq([x+y for x,y in zip(base,delta)])))
            self.assertLessEqual(sum((x-y)**2 for x,y in zip(a,b)),sum(d*d for d in delta))

    def test_exact_non_dyadic_charge(self):
        s=session(budget=Fraction(1))
        self.assertTrue(s.release(variance=Fraction(9,4)).accepted)
        self.assertEqual(s.spent,Fraction(8,9))
        self.assertFalse(s.release(variance=Fraction(9,4)).accepted)
        self.assertEqual(s.spent,Fraction(8,9))

    def test_public_parameters_rejected(self):
        s=session()
        for v in [0,-1,0.5,float("nan"),Fraction(0),Fraction(-1),Fraction(1,10**1000)]:
            with self.assertRaises(ValueError):
                s.release(variance=v)
        self.assertEqual(s.spent,0)

    def test_ingestion_validation(self):
        for rows in [[(-1,0,0)],[(1,2,0)],[(1,0,-1)],[(True,0,0)],[(1,0)]]:
            with self.assertRaises(ValueError):
                ReleaseSession(rows,cap=2,a_card=2,b_card=2,budget=Fraction(1))

    def test_one_session_concurrent_calls(self):
        s=session()
        with ThreadPoolExecutor(max_workers=2) as pool:
            results=list(pool.map(lambda _:s.release(variance=Fraction(4)),range(2)))
        self.assertEqual(sum(r.accepted for r in results),1)
        self.assertEqual(s.spent,Fraction(1,2))

    def test_independent_real_calls(self):
        # Output diversity is recorded, not used as a proof or flaky pass criterion.
        s=session(budget=Fraction(32))
        releases=[s.release(variance=Fraction(4)) for _ in range(32)]
        self.assertTrue(all(r.accepted for r in releases))
        self.assertEqual(s.spent,Fraction(16))
        OBSERVATIONS["real_releases_in_sequence"]=32
        OBSERVATIONS["distinct_observed_outputs"]=len({r.values for r in releases})


if __name__=="__main__":
    suite=unittest.defaultTestLoader.loadTestsFromTestCase(BackendTests)
    result=unittest.TextTestRunner(verbosity=2).run(suite)
    OBSERVATIONS.update(tests_run=result.testsRun,failures=len(result.failures),
                        errors=len(result.errors),success=result.wasSuccessful())
    (ROOT/"artifacts"/"opendp-tests.json").write_text(json.dumps(OBSERVATIONS,indent=2)+"\n")
    print(json.dumps(OBSERVATIONS,indent=2))
    sys.exit(0 if result.wasSuccessful() else 1)
