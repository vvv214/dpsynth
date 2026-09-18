"""Independent checks of GENERATED Python. These tests do not prove DP."""
import itertools
import json
import random
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parent
GEN = ROOT / 'artifacts' / 'flat_pipeline-py'
sys.path.insert(0, str(GEN))
sys.path.insert(0, str(ROOT))
import _dafny
import DataModel as DM
import FlatGrouping as FG
import FlatInput as FI
import GaussianGate as GG
import PrivacyCost as PC
import trusted_gaussian as backend

def raw(rows):
    return _dafny.Seq([FI.RawRecord_RawRecord(*r) for r in rows])

def typed(rows, a=2, b=2):
    ok, rs = FI.default__.Convert(raw(rows), a, b)
    assert ok
    return rs

def histogram(rows, cap, a=2, b=2):
    return list(FG.default__.FlatMarginal(typed(rows, a, b), cap, a, b))

def reference(rows, cap, a=2, b=2):
    used = {}
    h = [0] * (a*b)
    for uid,x,y in rows:
        count = used.get(uid, 0)
        if count < cap:
            h[x*b+y] += 1
            used[uid] = count+1
    return h

def frac(r):
    return Fraction(r.num,r.den)

def main():
    result = {'python': sys.version, 'exhaustive_histograms':0, 'user_removals':0,
              'random_histograms':0, 'grouping_checks':0}
    alphabet = [(0,0,0),(0,1,1),(1,0,1),(1,1,0)]
    for n in range(5):
        for rows in itertools.product(alphabet,repeat=n):
            rs = typed(rows)
            groups = FG.default__.GroupRecords(rs,2,2)
            ids = [g.uid for g in groups]
            assert len(ids)==len(set(ids))
            assert set(ids)=={r[0] for r in rows}
            for g in groups:
                assert [(c.a,c.b) for c in g.rows] == [(a,b) for u,a,b in rows if u==g.uid]
            result['grouping_checks'] += 1
            for cap in range(4):
                h = histogram(rows,cap)
                assert h == reference(rows,cap)
                result['exhaustive_histograms'] += 1
                for u in (0,1,2):
                    reduced = [r for r in rows if r[0]!=u]
                    h2 = histogram(reduced,cap)
                    delta = [x-y for x,y in zip(h,h2)]
                    assert all(x>=0 for x in delta)
                    assert sum(delta)<=cap
                    assert sum(x*x for x in delta)<=cap*cap
                    result['user_removals'] += 1
    rng = random.Random(4281)
    for _ in range(300):
        a,b=rng.randrange(1,5),rng.randrange(1,5)
        rows=[(rng.randrange(6),rng.randrange(a),rng.randrange(b)) for _ in range(rng.randrange(25))]
        cap=rng.randrange(6)
        assert histogram(rows,cap,a,b)==reference(rows,cap,a,b)
        result['random_histograms']+=1

    # Same UID in separated runs: one shared cap, not one cap per run.
    rows=[(7,0,1),(8,1,0),(7,0,1),(8,0,0),(7,1,1)]
    assert histogram(rows,2)==[1,2,1,0]
    prepared=GG.default__.CheckedBuild(raw(rows),2,2,2,4,1)
    assert prepared.is_Ready
    request=prepared.request
    assert frac(GG.default__.Cost(request))==Fraction(1,2)
    original=backend.default__.Sample
    calls=[]
    def recording(center,vn,vd):
        calls.append((list(center),vn,vd))
        return _dafny.Seq([_dafny.BigRational(x)+_dafny.BigRational(1,4) for x in center])
    backend.default__.Sample=staticmethod(recording)
    session=GG.default__.NewBudget(PC.Rat_Rat(3,4))
    ok,answer=session.Release(request)
    assert ok and len(answer)==4 and frac(session.Used())==Fraction(1,2)
    ok,answer=session.Release(request)
    assert not ok and list(answer)==[] and frac(session.Used())==Fraction(1,2)
    assert calls==[([1,2,1,0],4,1)]
    result['ffi_call_count_after_accept_then_reject']=len(calls)
    result['used_after_accept_then_reject']=str(frac(session.Used()))

    invalid=[([(-1,0,0)],2,2,2,4,1), ([(0,-1,0)],2,2,2,4,1),
             ([(0,0,-1)],2,2,2,4,1), ([(0,2,0)],2,2,2,4,1),
             ([(0,0,2)],2,2,2,4,1), (rows,-1,2,2,4,1),
             (rows,2,0,2,4,1), (rows,2,2,-1,4,1),
             (rows,2,2,2,0,1), (rows,2,2,2,4,0)]
    for values,cap,a,b,vn,vd in invalid:
        assert GG.default__.CheckedBuild(raw(values),cap,a,b,vn,vd).is_Rejected
    result['invalid_inputs_rejected']=len(invalid)
    # Backend exception consumes the reserved budget. No silent refund/retry.
    def failing(*_):
        raise RuntimeError('injected backend failure')
    backend.default__.Sample=staticmethod(failing)
    failed=GG.default__.NewBudget(PC.Rat_Rat(3,4))
    try:
        failed.Release(request)
        raise AssertionError('expected injected failure')
    except RuntimeError:
        assert frac(failed.Used())==Fraction(1,2)
    result['failure_keeps_charge']=True
    backend.default__.Sample=staticmethod(original)
    demo=GG.default__.NewBudget(PC.Rat_Rat(3,4))
    ok,noise=demo.Release(request)
    assert ok and len(noise)==4
    result['demo_gaussian_smoke']='passed; NOT sampler certification'
    # Exercise the iterative executable path beyond Python's default stack depth.
    big=[(i%30,i%2,(i//2)%2) for i in range(3000)]
    start=time.perf_counter()
    assert histogram(big,4)==reference(big,4)
    result['large_input_rows']=len(big)
    result['large_input_seconds']=round(time.perf_counter()-start,6)
    print(json.dumps(result,indent=2))
    print('FLAT_PIPELINE_TESTS_OK')
    (ROOT/'artifacts'/'tests.json').write_text(json.dumps(result,indent=2)+'\n')

if __name__=='__main__':
    main()
