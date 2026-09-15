"""Check reviewed PR264 source and explicit integration changes against base."""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess

parser = argparse.ArgumentParser()
parser.add_argument('--repo', type=Path, required=True)
parser.add_argument('--out', type=Path, required=True)
args = parser.parse_args()
repo = args.repo
base = '6d840cd6bdf811e166ba0a07501407fb121ff0ce'
source = '32b028cf16e210f8f628ab1cc7c8f5b389df0632'
canonical = 'matrix-functions-and-stability/MF-24/README.md'
package = 'references/mf24-counterexample/'
review = 'reviews/2026-09-15-pr264/'

def require(ok, reason):
    if not ok:
        raise RuntimeError(reason)

def git(*command):
    return subprocess.check_output(['git', '-C', str(repo), *command])

def blob(ref, path):
    return git('show', ref + ':' + path)

def files(ref):
    return {line.split(b'\t', 1)[1].decode(): line.split(b'\t', 1)[0]
            for line in git('ls-tree', '-rz', ref).split(b'\0') if line}

b, s = files(base), files(source)
require(set(b) <= set(s), 'Source deletes old file')
allowed = {'CATALOG.md', 'README.md', 'RESOLVED.md', canonical,
           'matrix-functions-and-stability/MF-24/problem.tex',
           'matrix-functions-and-stability/MF-24/problem.pdf',
           'matrix-functions-and-stability/README.md', 'tools/render_problems.py'}
require({p for p in b if b[p] != s[p]} == allowed, 'Unexpected source changes')
require(all(p.startswith(package) for p in set(s)-set(b)), 'Unexpected source additions')
require((repo/'problem_ids.json').read_bytes() == blob(base, 'problem_ids.json'), 'Registry changed')
registry = json.loads(blob(base, 'problem_ids.json'))
for ident, path in registry.items():
    original = blob(base, path)
    final = (repo/path).read_bytes()
    if ident != 'MF-24':
        require(final == original, 'Unrelated canonical page changed: '+ident)
        continue
    old, new = original.decode(), final.decode()
    require(old.splitlines()[0] == new.splitlines()[0], 'Title changed')
    for label in ['Topic', 'Difficulty', 'Importance', 'Rating rationale']:
        pattern = r'^\*\*' + label + r':\*\* (.+?)\s*$'
        require(re.search(pattern, old, re.M)[1] == re.search(pattern, new, re.M)[1], 'Original field changed: '+label)
    suffix = new[new.index('## Context and notation'):]
    suffix = suffix.replace('## Original scope and literature check\n\nThe following is the repository\'s pre-claim literature record, retained unchanged.\n\n\n', '## Scope and status check\n\n')
    require(suffix == old[old.index('## Context and notation'):], 'Original target/reference/history text changed')
    require('**Status:** Solved' in new and '**Last checked:** 2026-09-15' in new, 'Wrong final status/date')
package_files = []
for path in s:
    if path.startswith(package):
        original, final = blob(source, path), (repo/path).read_bytes()
        if path == package+'README.md':
            require(final.startswith(original), 'Source README changed before addendum')
            require(final[len(original):].startswith(b'\n## Maintainer assessment, 15 September 2026'), 'Unexpected package README append')
        else:
            require(original == final, 'Submitted file changed: '+path)
        package_files.append({'path': path, 'source_sha256': hashlib.sha256(original).hexdigest(), 'final_sha256': hashlib.sha256(final).hexdigest(), 'bytes_retained_exactly': original == final})
expected_renderer = blob(source, 'tools/render_problems.py').decode().replace('{"IE-05", "SP-15", "MF-02", "RE-03", "RA-01"}', '{"IE-05", "SP-15", "MF-02", "RE-03", "RA-01", "MF-24"}')
require((repo/'tools/render_problems.py').read_text() == expected_renderer, 'Unexpected renderer changes')
resolved = (repo/'RESOLVED.md').read_text()
start = resolved.index('### MF-24 —')
stop = resolved.index('### 🏆 MI-32', start)
require(resolved[:start]+resolved[stop:] == blob(base, 'RESOLVED.md').decode(), 'Prior resolution records changed')
def readme_prose(text):
    text = re.sub(r'<!-- catalog-summary -->.*?<!-- /catalog-summary -->', '', text, flags=re.S)
    return re.sub(r'\| Category \| Problems \|\n\| --- \| ---: \|\n(?:\|.*\n)+', '', text)
require(readme_prose((repo/'README.md').read_text()) == readme_prose(blob(base, 'README.md').decode()), 'Published README prose changed')
statuses = {}
for path in registry.values():
    status = re.search(r'^\*\*Status:\*\* (.+?)\s*$', (repo/path).read_text(), re.M)[1]
    statuses[status] = statuses.get(status, 0)+1
require(statuses == {'Open':42, 'Partially resolved':71, 'Solved':73, 'Lean verified':31}, 'Unexpected final status counts')
worktree_changes = {p for p in git('diff', '--name-only', source).decode().splitlines() if not p.startswith(review)}
require(worktree_changes == allowed | {package+'README.md'}, 'Unexpected integration change outside review bundle')
result = {'status':'PASS', 'base':base, 'source_head':source, 'source_tree':git('rev-parse',source+'^{tree}').decode().strip(), 'base_paths_retained':len(b), 'source_paths_retained':len(s), 'permanent_ids_unchanged':len(registry), 'unrelated_canonical_pages_byte_identical':216, 'original_target_references_and_history_preserved':True, 'historical_ratings_retained':True, 'published_readme_motivations_preserved':True, 'only_renderer_adjustment':'MF-24 joins Context-and-notation page-break set; source removal from References set retained', 'status_counts':statuses, 'open_targets':113, 'package_files':package_files, 'integration_exceptions':sorted(worktree_changes)}
args.out.write_text(json.dumps(result,indent=2)+'\n')
print(json.dumps({k:v for k,v in result.items() if k!='package_files'},indent=2))
