"""Run the finite exact regression suite and record its outcome."""
from pathlib import Path
import io
import argparse
import json
import platform
import sys
import time
import unittest

root=Path(__file__).resolve().parent
parser=argparse.ArgumentParser(description=__doc__)
parser.add_argument("--no-write",action="store_true",help="Run without modifying evidence files")
args=parser.parse_args()
start=time.perf_counter()
suite=unittest.defaultTestLoader.discover(str(root/"tests"))
stream=io.StringIO()
result=unittest.TextTestRunner(stream=stream,verbosity=2).run(suite)
text=stream.getvalue()
print(text,end="")
if not args.no_write:
    evidence=root/"evidence"
    evidence.mkdir(exist_ok=True)
    (evidence/"tests.log").write_text(text)
    (evidence/"verification.json").write_text(json.dumps({
        "tests_run":result.testsRun,"failures":len(result.failures),"errors":len(result.errors),
        "successful":result.wasSuccessful(),"elapsed_seconds":time.perf_counter()-start,
        "python":sys.version,"platform":platform.platform(),
        "scope":"Finite regression checks; not independent review or an asymptotic AC-06 proof"
    },indent=2)+"\n")
sys.exit(0 if result.wasSuccessful() else 1)
