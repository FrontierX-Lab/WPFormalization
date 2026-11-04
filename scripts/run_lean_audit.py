#!/usr/bin/env python3
"""Run a retained Lean audit, redirecting its artifact writes to _out/audit.
The original audit source is preserved; only literal output paths in the disposable
copy change. stdout/stderr are retained in the ignored output directory.
"""
from pathlib import Path
import subprocess, sys, re
ROOT = Path(__file__).resolve().parents[1]
source = (ROOT / sys.argv[1]).resolve()
assert source.is_relative_to(ROOT / 'audit') and source.suffix == '.lean'
out = ROOT / '_out/audit'
out.mkdir(parents=True, exist_ok=True)
code = source.read_text()
code = re.sub(r'(IO\.FS\.writeFile\s+")audit/', r'\1_out/audit/', code)
program = out / ('Run' + source.name)
program.write_text(code)
with (out / (source.stem + '.stdout.txt')).open('w') as log:
    result = subprocess.run(['lake','env','lean',str(program.relative_to(ROOT))], cwd=ROOT, stdout=log, stderr=subprocess.STDOUT)
print(f'{source.relative_to(ROOT)}: exit {result.returncode}')
raise SystemExit(result.returncode)
