"""Record a known specification gap. Never execute the mutated nonprivate code."""
import json
import os
from pathlib import Path
import shutil
import subprocess

ROOT=Path(__file__).resolve().parent
folder=ROOT/'artifacts'/'contract-scope-probe'
folder.mkdir(parents=True,exist_ok=True)
for name in ('FoundationPilot.dfy','FlatGrouping.dfy','GaussianGate.dfy','NumericBoundary.dfy'):
    shutil.copyfile(ROOT/name,folder/name)
p=folder/'GaussianGate.dfy'
s=p.read_text()
old='output := Backend.Sample(safeCenter,r.cap,r.varianceNum,r.varianceDen);'
new='output := seq(|safeCenter|, i => AtOrZero(safeCenter,i) as real);'
assert s.count(old)==1
p.write_text(s.replace(old,new))
result=subprocess.run([os.environ.get('DAFNY','dafny'),'verify',str(p),
    '--filter-symbol=GaussianGate.Budget.Release','--verification-time-limit','15'],
    capture_output=True,text=True,timeout=45)
(folder/'verify.log').write_text(result.stdout+result.stderr)
report={
    'probe':'replace trusted sampler call by raw saturated histogram',
    'verifier_exit_code':result.returncode,
    'mutant_accepted':result.returncode==0,
    'mutant_executed':False,
    'status':'KNOWN CONTRACT GAP, NOT A PRIVACY CERTIFICATION',
    'explanation':'Shape and accounting contracts do not constrain output provenance.',
    'counterexample':{'cap':2,'schema':[2,2],'D':[],"D_prime":[[1,0,0]],
                      'event':'first output cell equals 1',
                      'event_probability_D':0,'event_probability_D_prime':1},
}
(folder/'result.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps(report,indent=2))
# This diagnostic preserves the gap as an explicit expected result. Changing
# the release contract should also change this test, not silently omit it.
if result.returncode!=0:
    raise SystemExit('Contract-scope probe changed; inspect its log before updating expectations')
