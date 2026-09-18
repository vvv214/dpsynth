#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")"
DAFNY="${DAFNY:-dafny}"
export DAFNY
mkdir -p artifacts
"$DAFNY" --version | tee artifacts/dafny-version.txt
python3 --version 2>&1 | tee artifacts/python-version.txt
"$DAFNY" verify GaussianGate.dfy --verify-included-files --verification-time-limit 30 2>&1 | tee artifacts/verify.log
"$DAFNY" audit GaussianGate.dfy --report-file artifacts/audit.md
"$DAFNY" translate py GaussianGate.dfy --verify-included-files --include-runtime --output=artifacts/flat_pipeline 2>&1 | tee artifacts/translate.log
python3 test_generated.py | tee artifacts/python-tests.log
python3 check_negative.py | tee artifacts/negative-tests.log
find . -maxdepth 1 -type f \( -name '*.dfy' -o -name '*.py' -o -name '*.sh' \) -print0 | sort -z | xargs -0 sha256sum > artifacts/source-sha256.txt
find artifacts/flat_pipeline-py -type f -name '*.py' -print0 | sort -z | xargs -0 sha256sum > artifacts/generated-sha256.txt
