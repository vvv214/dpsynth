"""Require verification/access-control rejection of intentionally bad variants."""
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
import json
import os
import shutil
import subprocess

ROOT = Path(__file__).resolve().parent
DAFNY = os.environ.get('DAFNY', 'dafny')
SOURCES = ('FoundationPilot.dfy','FlatGrouping.dfy','GaussianGate.dfy','NumericBoundary.dfy')
CASES = {
  'bypass_integer_saturation': ('GaussianGate.dfy','var safeCenter := NB.Saturate(r.center);','var safeCenter := r.center;'),
  'bypass_clipping': ('FlatGrouping.dfy','rows:=rows+ClipRows(db[i].rows,cap);','rows:=rows+db[i].rows;'),
  'omit_budget_charge': ('GaussianGate.dfy','      used := next;','      used := used;'),
  'underestimate_sensitivity': ('GaussianGate.dfy','Rat(r.cap*r.cap*r.varianceDen,2*r.varianceNum)','Rat(r.cap*r.varianceDen,2*r.varianceNum)'),
}
FILTERS = {'bypass_integer_saturation':'GaussianGate.Budget.Release','bypass_clipping':'FlatGrouping.FlatMarginal',
           'omit_budget_charge':'GaussianGate.Budget.Release',
           'underestimate_sensitivity':'GaussianGate.Build'}
CLIENTS = {
 'forge_request': '''module NegativeClient {
  import opened GaussianGate
  method Forge() returns (r:Request) { r := Request([],1,1,1,1,1); }
}''',
 'bypass_private_backend': '''module NegativeClient {
  import G = GaussianGate
  import B = G.GaussianBackend
}''',
 'reset_private_budget': '''module NegativeClient {
  import opened GaussianGate
  import opened PrivacyCost
  method Reset(s:Budget) modifies s { s.used := ZeroRat(); }
}''',
}

def run_one(name):
    folder = ROOT/'artifacts'/'negative'/name
    folder.mkdir(parents=True,exist_ok=True)
    for source in SOURCES:
        shutil.copyfile(ROOT/source,folder/source)
    target='GaussianGate.dfy'
    expected=4
    if name in CASES:
        filename,old,new=CASES[name]
        path=folder/filename
        text=path.read_text()
        assert text.count(old)==1,(name,text.count(old))
        path.write_text(text.replace(old,new,1))
    else:
        target='NegativeClient.dfy'
        (folder/target).write_text('include "GaussianGate.dfy"\n'+CLIENTS[name]+'\n')
        expected=2
    command=[DAFNY,'verify',target,'--verify-included-files','--verification-time-limit','15']
    # The positive run already verifies every source. Each mutation rechecks the affected obligation.
    if name in FILTERS:
        command += ['--filter-symbol',FILTERS[name]]
    completed=subprocess.run(command,cwd=folder,
                             capture_output=True,text=True,timeout=70)
    log=completed.stdout+completed.stderr
    (folder/'verify.log').write_text(log)
    # A timeout, missing executable, parse failure for a mutation, or signal is NOT a detected bug.
    accepted=(completed.returncode==expected and 'Error:' in log and
              'timed out' not in log.lower() and 'parse errors' not in log.lower())
    row={'case':name,'exit_code':completed.returncode,'expected_exit_code':expected,
         'rejected_as_expected':accepted}
    print(json.dumps(row),flush=True)
    return row

if __name__=='__main__':
    with ThreadPoolExecutor(max_workers=2) as pool:
        results=list(pool.map(run_one,list(CASES)+list(CLIENTS)))
    (ROOT/'artifacts'/'negative-results.json').write_text(json.dumps(results,indent=2)+'\n')
    if not all(r['rejected_as_expected'] for r in results):
        raise SystemExit('Negative test failure; inspect logs.')
    print('NEGATIVE_CHECKS_OK')
