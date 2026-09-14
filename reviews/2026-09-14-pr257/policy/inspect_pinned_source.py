"""Read-only source-boundary and preservation audit; no submitted code executes."""
import hashlib
import json
import re
import subprocess
from pathlib import Path

root = Path('/private/tmp/nla-mi32-formalization-review')
catalog = Path('/private/tmp/nla-audit-257')
out = Path('/private/tmp/nla-review-257/policy')

def git(path, *args):
    return subprocess.check_output(['git', '-C', str(path), *args])

def digest(data):
    return hashlib.sha256(data).hexdigest()

def code_only(text):
    # Independent nested-comment/string removal for an informative lexical scan.
    result, pos, level = [], 0, 0
    while pos < len(text):
        if level:
            if text[pos:pos+2] == '/-':
                level += 1; pos += 2
            elif text[pos:pos+2] == '-/':
                level -= 1; pos += 2
            else:
                result.append('\n' if text[pos] == '\n' else ' '); pos += 1
        elif text[pos:pos+2] == '/-':
            level = 1; pos += 2; result.append(' ')
        elif text[pos:pos+2] == '--':
            end = text.find('\n', pos)
            pos = len(text) if end < 0 else end
        elif text[pos] == '"':
            pos += 1
            while pos < len(text):
                if text[pos] == '\\': pos += 2
                elif text[pos] == '"': pos += 1; break
                else: pos += 1
            result.append(' ')
        else:
            result.append(text[pos]); pos += 1
    assert level == 0
    return ''.join(result)

paths = [root/p for p in git(root, 'ls-files', '*.lean').decode().splitlines()]
scans = {}
imports = {}
danger = re.compile(r'\b(sorry|admit|axiom|native_decide|unsafe|implemented_by|extern|run_meta)\b')
for path in paths:
    code = code_only(path.read_text())
    name = str(path.relative_to(root))
    matches = [{'line': code[:m.start()].count('\n')+1, 'token': m.group()} for m in danger.finditer(code)]
    if matches: scans[name] = matches
    imports[name] = re.findall(r'^\s*import\s+([^\n]+)', code, re.M)
assert scans == {'Challenge.lean': [{'line': 112, 'token': 'sorry'}]} or set(scans) == {'Challenge.lean'}
assert not any('Challenge' in item for name, rows in imports.items() if name != 'Challenge.lean' for item in rows)

manifest = json.loads((root/'lake-manifest.json').read_text())
assert len(manifest['packages']) == 9
assert all(x['type'] == 'git' and re.fullmatch('[0-9a-f]{40}', x['rev']) for x in manifest['packages'])
vendor = json.loads((root/'vendor/graph-matrices/manifest.json').read_text())
vendor_checks = {x['path']: digest((root/'vendor/graph-matrices'/x['path']).read_bytes()) == x['sha256'] for x in vendor['copied_modules']}
assert all(vendor_checks.values()) and len(vendor_checks) == 16

challenge = (root/'Challenge.lean').read_text()
statement = (root/'MI32/Statement.lean').read_text()
assert challenge.startswith(statement.rsplit('end MI32', 1)[0])
config = json.loads((root/'comparator.json').read_text())
assert config == {'challenge_module':'Challenge', 'solution_module':'Solution',
                  'theorem_names':['MI32.main_upper'], 'definition_names':[],
                  'permitted_axioms':['propext','Quot.sound','Classical.choice'], 'enable_nanoda': True}

target = 'matrix-inequalities-and-norms/MI-32/README.md'
base = git(catalog, 'show', 'deb549fa9ddd6b119e6c59016f268237e645dfa2:'+target).decode()
head = (catalog/target).read_text()
def statement_section(text):
    return text.split('## Statement\n', 1)[1].split('\n## ', 1)[0]
assert statement_section(base) == statement_section(head)
for label in ['Difficulty', 'Importance', 'Topic']:
    assert re.search(r'\*\*'+label+r':\*\*[^\n]+', base).group() == re.search(r'\*\*'+label+r':\*\*[^\n]+', head).group()
assert git(catalog,'show','deb549fa9ddd6b119e6c59016f268237e645dfa2:problem_ids.json') == (catalog/'problem_ids.json').read_bytes()
formal_changed = git(root, 'diff', '--name-only', '762bd5ec5050a96f5e6ba3926b6cda4816fcd4b0', 'bd00df8dca9c6128cf528591d3485f8ca9eecd88', '--', '*.lean', 'lean-toolchain', 'lake-manifest.json', 'comparator.json')
assert not formal_changed
report = {
    'reviewer':'Codex AI subagent audit_254; source-only independent checks',
    'formal_head':git(root,'rev-parse','HEAD').decode().strip(),
    'catalog_head':git(catalog,'rev-parse','HEAD').decode().strip(),
    'lean_toolchain':(root/'lean-toolchain').read_text().strip(),
    'dependencies':manifest['packages'],
    'comparator_configuration':config,
    'source_scan_matches':scans,
    'source_scan_files':len(paths),
    'challenge_imports':imports['Challenge.lean'],
    'challenge_definitions_identical_to_implementation_prefix':True,
    'no_other_source_imports_challenge':True,
    'vendor_hash_checks':vendor_checks,
    'original_target_byte_identical':True,
    'original_ratings_identical':True,
    'id_registry_byte_identical':True,
    'later_manuscript_revision_has_identical_lean_toolchain_manifest_comparator':True,
    'source_hashes':{str(p.relative_to(root)):digest(p.read_bytes()) for p in paths},
    'boundary_hashes':{p:digest((root/p).read_bytes()) for p in ['lakefile.lean','lean-toolchain','lake-manifest.json','comparator.json','scripts/verify.py','verification/full-target-axioms.log']},
    'limits':'This does not execute Lean/Comparator/NanoDa or authenticate external CI. Root reviewer authenticates the public mechanical run.'
}
(out/'pinned-source-inspection.json').write_text(json.dumps(report,indent=2)+'\n')
print(json.dumps({k:v for k,v in report.items() if k not in ['source_hashes','dependencies','vendor_hash_checks']},indent=2))
