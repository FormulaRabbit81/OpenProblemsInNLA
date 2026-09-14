"""Read-only source checks for PR 257; does not compile or execute Lean."""
from pathlib import Path
import hashlib
import json
import re
import subprocess

PROOF = Path('/private/tmp/nla-mi32-formalization-review')
CATALOG = Path('/private/tmp/nla-audit-257')
OUT = Path('/private/tmp/nla-review-257')
BASE = 'deb549fa9ddd6b119e6c59016f268237e645dfa2'
EXPECTED_PR = 'cc661b4170e590daeb2ca4232336ab8b6d2eeaaf'
EXPECTED_PROOF = '762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0'
PAGE = 'matrix-inequalities-and-norms/MI-32/README.md'

def git(root, *args):
    return subprocess.check_output(['git', '-C', str(root), *args], text=True)

def sha(data):
    return hashlib.sha256(data).hexdigest()

def strip_comments(src):
    # Nested Lean block comments, line comments, and quoted strings. Newlines
    # survive so findings retain original source line numbers.
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(src):
        pair = src[i:i+2]
        if depth:
            if pair == '/-': depth += 1; out.extend('  '); i += 2
            elif pair == '-/': depth -= 1; out.extend('  '); i += 2
            else: out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif string:
            if src[i] == '\\' and i + 1 < len(src): out.extend('  '); i += 2
            elif src[i] == '"': string = False; out.append(' '); i += 1
            else: out.append('\n' if src[i] == '\n' else ' '); i += 1
        elif pair == '/-': depth = 1; out.extend('  '); i += 2
        elif pair == '--':
            j = src.find('\n', i)
            if j == -1: j = len(src)
            out.extend(' ' * (j-i)); i = j
        elif src[i] == '"': string = True; out.append(' '); i += 1
        else: out.append(src[i]); i += 1
    assert depth == 0 and not string
    return ''.join(out)

def section(src):
    return re.search(r'^## Statement\n.*?(?=^## |\Z)', src, re.M | re.S).group()

def local_path(module):
    rel = Path(*module.split('.')).with_suffix('.lean')
    for candidate in (PROOF / rel, PROOF / 'vendor/graph-matrices' / rel):
        if candidate.exists(): return candidate
    return None

assert git(CATALOG, 'rev-parse', 'HEAD').strip() == EXPECTED_PR
assert git(PROOF, 'rev-parse', 'HEAD').strip() == EXPECTED_PROOF
old = git(CATALOG, 'show', f'{BASE}:{PAGE}')
new = (CATALOG / PAGE).read_text()
assert section(old) == section(new)

statement = strip_comments((PROOF / 'MI32/Statement.lean').read_text())
challenge = strip_comments((PROOF / 'Challenge.lean').read_text())
norm = lambda text: re.sub(r'\s+', ' ', text).strip()
stmt_defs = statement[:statement.rfind('end MI32')]
challenge_defs = challenge[:challenge.index('theorem main_upper')]
assert norm(stmt_defs) == norm(challenge_defs)
declarations = re.findall(r'^def (\w+)', stmt_defs, re.M)
assert declarations == ['moment', 'spectralNorm', 'varianceScale', 'deletedBilinear',
                        'weakMoment', 'deletionScale', 'RegularEntries', 'UpperBoundAt']

seen = {}
external = set()
stack = ['Solution']
danger = []
while stack:
    module = stack.pop()
    if module in seen: continue
    path = local_path(module)
    if path is None:
        external.add(module)
        continue
    raw = path.read_text()
    code = strip_comments(raw)
    imports = re.findall(r'^import\s+([A-Za-z0-9_.]+)\s*$', code, re.M)
    for match in re.finditer(r'\b(?:sorry|sorryAx|admit|axiom|unsafe|implemented_by|native_decide)\b', code):
        danger.append({'file': str(path.relative_to(PROOF)),
                       'line': code.count('\n', 0, match.start()) + 1,
                       'token': match.group()})
    seen[module] = {'path': str(path.relative_to(PROOF)), 'sha256': sha(path.read_bytes()),
                    'imports': imports, 'lines': len(raw.splitlines())}
    stack.extend(imports)
assert 'Challenge' not in seen
assert not danger, danger
assert all(module.startswith(('Mathlib.', 'Lean.')) for module in external), sorted(external)

result = {
    'scope': 'Static semantic/source inspection; not a Lean build, Comparator run, or NanoDa replay.',
    'pr_head': EXPECTED_PR, 'proof_head': EXPECTED_PROOF, 'published_base': BASE,
    'canonical_statement_byte_identical': True,
    'canonical_statement_sha256': sha(section(new).encode()),
    'challenge_and_statement_definitions_token_identical': True,
    'target_definitions': declarations,
    'solution_local_import_closure_count': len(seen),
    'solution_local_import_closure_lines': sum(x['lines'] for x in seen.values()),
    'challenge_in_solution_import_closure': False,
    'dangerous_tokens_in_comment_stripped_local_closure': danger,
    'external_imports': sorted(external),
    'local_modules': dict(sorted(seen.items())),
    'primary_pdf_sha256': sha((OUT / 'latala-swiatkowski-2106.03139v2.pdf').read_bytes()),
    'proof_worktree_status': git(PROOF, 'status', '--porcelain'),
    'catalog_worktree_status': git(CATALOG, 'status', '--porcelain'),
}
(OUT / 'semantic-source-checks.json').write_text(json.dumps(result, indent=2) + '\n')
print(json.dumps({k: v for k, v in result.items() if k not in {'external_imports', 'local_modules'}}, indent=2))
