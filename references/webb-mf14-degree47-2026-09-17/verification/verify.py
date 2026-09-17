#!/usr/bin/env python3
"""Fail-closed reproduction of the frozen exact degree47 certificate package.

The original research files are never executed in place or modified. Assertions
in the frozen checkers remain enabled: this runner refuses optimized Python and
starts every child with -E, without -O, so PYTHONOPTIMIZE cannot affect children.
All new trust-boundary checks below use explicit exceptions, not assertions.
"""
from fractions import Fraction
from pathlib import Path, PurePosixPath
import argparse
import hashlib
import json
import math
import os
import shutil
import subprocess
import sys
import tempfile

HERE = Path(__file__).resolve().parent
PACKAGE = HERE.parent
SOURCE = PACKAGE / 'source'
MANIFEST = HERE / 'input_manifest.json'
EXPECTED_MANIFEST_SHA256 = '953116f9dd40f8c584a2f9cf1af840533c37ff9ced08f741ae901658f917d68b'
AUTHOR_SCRIPT = 'experiments/lower_full49_certify.py'
AUTHOR_RESULT = 'experiments/lower_full49_certify.json'
REVIEW_SCRIPT = 'reviews/full49-degree47-fresh-check.py'
REVIEW_RESULT = 'reviews/full49-degree47-fresh-check.json'
SEED = 'experiments/lower_full49_seed.json'


class VerificationError(RuntimeError):
    pass


def require(condition, message):
    if not condition:
        raise VerificationError(message)


def digest(data):
    return hashlib.sha256(data).hexdigest()


def read_json(path):
    try:
        return json.loads(path.read_bytes())
    except (OSError, ValueError) as exc:
        raise VerificationError(f'Cannot read JSON {path.name}: {exc}') from exc


def validate_inputs():
    require(not MANIFEST.is_symlink(), 'The input manifest must not be a symlink')
    raw = MANIFEST.read_bytes()
    require(digest(raw) == EXPECTED_MANIFEST_SHA256, 'Frozen input manifest hash mismatch')
    data = json.loads(raw)
    require(data.get('schema_version') == 1, 'Unsupported input manifest schema')
    records = data.get('inputs')
    require(isinstance(records, dict) and len(records) == 10, 'Expected exactly ten frozen source inputs')
    require(SOURCE.is_dir() and not SOURCE.is_symlink(), 'Missing or symlinked source directory')
    found = set()
    for path in SOURCE.rglob('*'):
        require(not path.is_symlink(), f'Symlink in frozen source: {path.relative_to(SOURCE)}')
        if path.is_file():
            found.add(path.relative_to(SOURCE).as_posix())
    require(found == set(records), 'Frozen source file set differs from the manifest')
    for name, record in records.items():
        rel = PurePosixPath(name)
        require(not rel.is_absolute() and '..' not in rel.parts, f'Unsafe manifest path: {name}')
        content = (SOURCE / name).read_bytes()
        require(len(content) == record.get('bytes'), f'Frozen input size mismatch: {name}')
        require(digest(content) == record.get('sha256'), f'Frozen input hash mismatch: {name}')
    return data


def fraction(data, key):
    require(isinstance(data.get(key), str), f'Expected exact fraction string: {key}')
    try:
        return Fraction(data[key])
    except (ValueError, ZeroDivisionError) as exc:
        raise VerificationError(f'Invalid exact fraction: {key}') from exc


def validate_result(result, independent=False):
    require(result.get('status') == 'PASS', 'Checker did not report PASS')
    require(result.get('degree') == 47 and result.get('parameter_count') == 49,
            'Checker result has the wrong degree or parameter count')
    active = result.get('active_parameters')
    require(isinstance(active, list) and len(active) == 48 and len(set(active)) == 48,
            'Active parameter indices must be 48 distinct entries')
    require(all(type(i) is int and 0 <= i < 49 for i in active), 'Invalid active parameter index')
    eta = fraction(result, 'preconditioned_residual_bound')
    defect = fraction(result, 'inverse_defect_bound')
    inverse = fraction(result, 'inverse_norm_bound')
    radius = fraction(result, 'radius')
    require(radius == Fraction(1, 10**45), 'Unexpected contraction radius')
    require(0 <= eta < Fraction(1, 10**69), 'Residual bound failed')
    require(0 <= defect < Fraction(1, 10**57), 'Inverse defect bound failed')
    require(0 < inverse < 4000, 'Inverse norm bound failed')
    require(fraction(result, 'b_real_distance_from_2') > radius, 'Actual-circuit chart b != 2 is not certified')
    if independent:
        require(result.get('full_polynomial_degree') == 128, 'Independent reconstruction is not full degree128')
        require(result.get('parameter_degree_bound') == 33, 'Unexpected parameter degree bound')
        require(result.get('exact_author_eta_defect_inverse_norm_match') is True,
                'Independent rational bounds do not match the author certificate')
        hessian = fraction(result, 'independent_hessian_bound')
        contraction = fraction(result, 'independent_contraction_bound')
        self_map = fraction(result, 'independent_self_map_bound')
        require(result.get('contraction_less_than_half') is True and result.get('self_map_strictly_inside_ball') is True,
                'Independent checker did not certify both contraction conditions')
    else:
        hessian = fraction(result, 'Hessian_bound')
        contraction = fraction(result, 'contraction_bound')
        self_map = fraction(result, 'self_map_bound')
        require(0 < hessian < 2 * 10**12, 'Author Hessian bound failed')
    require(hessian > 0, 'Hessian bound must be positive')
    require(contraction == defect + inverse * hessian * radius, 'Contraction formula mismatch')
    require(self_map == eta + contraction * radius, 'Self-map formula mismatch')
    require(0 <= contraction < Fraction(1, 2), 'Contraction is not strict')
    require(0 <= self_map < radius, 'The closed ball is not mapped strictly inside itself')


def run_child(command, cwd):
    try:
        result = subprocess.run(command, cwd=cwd, text=True, stdout=subprocess.PIPE,
                                stderr=subprocess.STDOUT, timeout=180)
    except (OSError, subprocess.TimeoutExpired) as exc:
        raise VerificationError(f'Checker execution failed: {exc}') from exc
    require(result.returncode == 0,
            f'Checker exited with status {result.returncode}:\n{result.stdout}')
    return result.stdout


def reproduce(output_dir, manifest):
    require(not output_dir.resolve().is_relative_to(SOURCE.resolve()), 'Output directory must be outside frozen source')
    output_dir.mkdir(parents=True, exist_ok=True)
    child_prefix = [sys.executable, '-E', '-B', '-s']
    probe = run_child(child_prefix + ['-c',
        'import json,sys; print(json.dumps({"optimize":sys.flags.optimize,"ignore_environment":sys.flags.ignore_environment,"dont_write_bytecode":sys.flags.dont_write_bytecode}))'], HERE)
    flags = json.loads(probe)
    require(flags == {'optimize': 0, 'ignore_environment': 1, 'dont_write_bytecode': 1},
            'Child interpreter does not preserve assertions and ignore Python environment variables')
    archived_author = read_json(SOURCE / AUTHOR_RESULT)
    archived_review = read_json(SOURCE / REVIEW_RESULT)
    validate_result(archived_author)
    validate_result(archived_review, independent=True)
    with tempfile.TemporaryDirectory(prefix='mf14-degree47-verify-') as temp:
        isolated = Path(temp) / 'source'
        shutil.copytree(SOURCE, isolated)
        for name, record in manifest['inputs'].items():
            require(digest((isolated / name).read_bytes()) == record['sha256'], f'Isolated copy mismatch: {name}')
        author_log = run_child(child_prefix + [str(isolated / AUTHOR_SCRIPT)], isolated)
        author_bytes = (isolated / AUTHOR_RESULT).read_bytes()
        require(digest(author_bytes) == manifest['inputs'][AUTHOR_RESULT]['sha256'],
                'Regenerated author certificate differs from its frozen bytes')
        author_result = json.loads(author_bytes)
        validate_result(author_result)
        review_log = run_child(child_prefix + [str(isolated / REVIEW_SCRIPT)], isolated)
        review_result = read_json(isolated / REVIEW_RESULT)
        validate_result(review_result, independent=True)
        require(review_result.get('seed_sha256') == manifest['inputs'][SEED]['sha256'], 'Independent result is bound to a different seed')
        require(review_result.get('author_certificate_sha256') == manifest['inputs'][AUTHOR_RESULT]['sha256'],
                'Independent result is bound to a different author certificate')
        elapsed = review_result.get('elapsed_seconds')
        require(type(elapsed) in (int, float) and math.isfinite(elapsed) and elapsed >= 0,
                'Invalid independent-checker runtime metadata')
        # The frozen independent checker records runtime; every mathematical field
        # and full-array digest must match the reviewed archival result exactly.
        stable_review = {k: v for k, v in review_result.items() if k != 'elapsed_seconds'}
        stable_archived = {k: v for k, v in archived_review.items() if k != 'elapsed_seconds'}
        require(stable_review == stable_archived, 'Independent mathematical certificate differs from the frozen review')
        require(author_result['active_parameters'] == review_result['active_parameters'], 'Active-index mismatch between checkers')
        (output_dir / 'author-checker.log').write_text(author_log, encoding='utf-8')
        (output_dir / 'independent-checker.log').write_text(review_log, encoding='utf-8')
        (output_dir / 'author-result.json').write_bytes(author_bytes)
        (output_dir / 'independent-result.json').write_text(json.dumps(review_result, indent=2) + '\n', encoding='utf-8')
    # Detect any unintended in-place write or source mutation during reproduction.
    validate_inputs()
    summary = {
        'status': 'PASS', 'degree': 47, 'frozen_input_count': 10,
        'input_manifest_sha256': EXPECTED_MANIFEST_SHA256,
        'runner_sha256': digest(Path(__file__).read_bytes()),
        'python_version': sys.version, 'child_flags': flags,
        'parent_pythonoptimize_environment_present': 'PYTHONOPTIMIZE' in os.environ,
        'checkers_ran_in_temporary_copy': True, 'frozen_source_revalidated_after_run': True,
        'author_certificate_byte_identical': True,
        'independent_certificate_identical_except_elapsed_seconds': True,
        'full_degree128_reverse_arrays_sha256': review_result['full_arrays_stream_sha256'],
        'scope': 'Exact certificate reconstruction; the separate frozen proof and independent review justify actual-product membership, the full coefficient limit, and the matching upper bound.'
    }
    (output_dir / 'summary.json').write_text(json.dumps(summary, indent=2) + '\n', encoding='utf-8')
    return summary


def main():
    require(sys.flags.optimize == 0,
            'Optimized Python is refused: frozen checker assertions must remain enabled (do not use -O/-OO or PYTHONOPTIMIZE).')
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--output-dir', type=Path, default=HERE / 'reproduction')
    parser.add_argument('--check-inputs-only', action='store_true', help='Validate the frozen manifest and source bytes without running certificates')
    args = parser.parse_args()
    manifest = validate_inputs()
    if args.check_inputs_only:
        print('PASS: frozen manifest and all ten source inputs match')
        return 0
    summary = reproduce(args.output_dir, manifest)
    print('PASS: both exact degree47 checkers reproduced; full degree128 reconstruction matches')
    print('Summary:', args.output_dir / 'summary.json')
    return 0


if __name__ == '__main__':
    try:
        sys.exit(main())
    except (VerificationError, OSError, ValueError, KeyError, TypeError) as exc:
        print(f'FAIL: {exc}', file=sys.stderr)
        sys.exit(2)
