from pathlib import Path
import hashlib,json,subprocess
p=Path(__file__).resolve().parents[1]
h=lambda b:hashlib.sha256(b).hexdigest()
receipt=json.loads((p/'statement-typecheck.json').read_text())
assert receipt['exit_code']==0
for f,v in receipt['files'].items():assert h((p/f).read_bytes())==v,(f,'stale build receipt')
files=['NLA/KE05/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','formalization.yaml','comparator.json','SOURCE_PROVENANCE.json','lakefile.toml','lake-manifest.json','lean-toolchain','statement-typecheck.json','statement-typecheck.log','reviews/referee-1-exact-check.py','reviews/referee-1-exact-check.json','reviews/referee-1-record.py']
imports=['Probability/Distributions/Gaussian/Real.lean','MeasureTheory/Constructions/Pi.lean','Analysis/CStarAlgebra/Matrix.lean','LinearAlgebra/Matrix/NonsingularInverse.lean','Order/ConditionallyCompleteLattice/Basic.lean']
files+=['.lake/packages/mathlib/Mathlib/'+x for x in imports]
inputs={f:h((p/f).read_bytes()) for f in files}
prov=json.loads((p/'SOURCE_PROVENANCE.json').read_text());sources={}
repo='/Users/sholden/Projects/OpenProblemsInNLA'
for f in prov['source_files']:
 b=subprocess.check_output(['git','show',prov['source_commit']+':'+f['repository_path']],cwd=repo)
 assert h(b)==f['sha256']
 sources[f['repository_path']]=h(b)
comp=json.loads((p/'comparator.json').read_text())
assert len(comp['theorem_names'])==10 and not comp['definition_names']
assert set(comp['permitted_axioms'])=={'propext','Classical.choice','Quot.sound'}
r={'verdict':'APPROVE','phase':'statements only','reviewer':'independent AI agent /root/iv06_statement_referee_2 (report slot 1)','source_commit':prov['source_commit'],'statement_build_exit_code':0,'statement_build_attribution':'Draft author/coordinator run; receipt and complete log independently inspected and hashes matched; not independently rerun','independent_exact_diagnostic_exit_code':0,'export_count':10,'source_sha256':sources,'inputs_sha256':inputs,'limitations':['No proof bodies inspected or implemented.','Ten Challenge sorry declarations are deliberate and establish no theorem.','Finite exact diagnostics are not probability proofs.','No completed LeanCert trust or Linux Comparator claim.']}
(p/'reviews/referee-1-statement-checks.json').write_text(json.dumps(r,indent=2)+'\n')
body='''# KE-05 independent statement review 1

**APPROVE — statements only.** Reviewer: independent AI agent `/root/iv06_statement_referee_2`, not the boundary author. This applies the repository’s Tau Ceti adaptation, not an official Tau Ceti service or human peer review. No active proof or Solution was inspected or implemented.

I read the complete canonical README and complete Stepaniants solution (including Sections 1–5 and scope notes) at preserved source `deb549fa9ddd6b119e6c59016f268237e645dfa2`, all proposed definitions and ten Challenge signatures, numerical plan, metadata and Comparator configuration. Source hashes were independently matched against Git. This records that preserved source, not a claim about current upstream main.

## Fidelity and nonvacuity

The final conjecture quantifies arbitrary positive block size, at least two blocks, each failure tolerance, a finite real constant, and then every deterministic admissible real diagonal input. Admissibility excludes common eigenvalues between blocks only; repeated eigenvalues within a block and interlacing remain permitted. The actual finite product of `gaussianReal 0 1` has one coordinate for each matrix entry and is a probability measure. The input is outside its probability event. The final fixed b=2,d=3 contradiction therefore negates the full canonical target; it does not replace it by a scalar-only or sample-dependent claim.

I checked the descending fold for the outer recurrence and the ascending dropped/taken list for the inner recurrence. `rootOrder` is exactly the prescribed first-root order; the exported whole-list equality prevents an indexing default from changing it. Updates to lower positions cannot alter the higher hats already used. The contract requires actual final arrays to satisfy the original formulas, including i=d−1 with its empty product. All inverses are actual Mathlib nonsingular inverses. `Valid` includes every original Omega and every Omega*S; together these give nonsingular S as required for the coefficient inverse. Probability-one validity for every admissible input is an explicit export, not a hidden assumption.

`Matrix.toEuclideanCLM` maps to continuous linear maps of EuclideanSpace; its norm is the intended spectral norm. Actual real sInf/sSup define endpoints, cross-gap and maxima. Their underlying sets are finite and nonempty for b≥1,d≥2, hence bounded, so these are genuine extrema. Future proofs must supply those finiteness/nonemptiness/boundedness obligations when using conditionally complete lattice lemmas. The ordering-specific monomial maximum excludes only the first block, includes both endpoints and 1, and implements exactly the stated simultaneous numerator/denominator-zero convention. Coefficient exponents and gaps match the source. The two global maxima are taken separately before multiplication.

The zero value on the invalid event is harmless only after the demanded probability-one validity theorem. The export also demands measurability of the actual total constant; the real event probability is the toReal of its measure under the probability law. No singular outcome or empty-set totalization can establish the final result by itself.

## Exact reconstruction and proof obligations

The independent rational diagnostic reconstructs X, P, kappa=7, Q and N, verifies det N=0 and Frobenius-square (68/7)^2 (hence the stated rank-one spectral norm), and evaluates every root ordering for three rational epsilon values. It checks the determinant and transformed-block formulas and the consistency of the final arrays with the literal inner recurrence. Finite list indexing is additionally checked through d=9. These checks are retained as a reproducible script and JSON and are not presented as universal or probability proofs.

The epsilon shift is exact: natural m≥0 with 1/(m+6) is the manuscript sequence m≥1 with 1/(m+5). The lower bound retains actual global constants and the coefficient factor 8^(−1/4). The rational sample establishes nonzero polynomial witnesses only; it is never assigned positive Gaussian probability. All-order almost-sure validity, nonvanishing kappa and Q00, convergence of the actual transformed block, divergence, and the marginal probability limit remain actual exported obligations. These are substantial formalization work, not assumed infrastructure. Every finite real C must admit a deterministic counterexample with probability below 1/2, yielding the full negation.

## Reuse, attribution and mechanical scope

I inspected pinned Mathlib’s Gaussian definition and probability instance, finite product measure, Euclidean continuous-linear-map matrix equivalence, total inverse identities, and the nonempty/bounded hypotheses of csSup/csInf APIs. These are suitable existing semantics; there are no custom probability or norm substitutes. Exact 2-by-2 algebra and finite rational witnesses appropriately minimize computation. The full polynomial-null-set and dominated-convergence bridges cannot be replaced by finite checks.

George Stepaniants receives proof credit, Nian Shao framework/conjecture credit, and Sidney Holden the AI-assisted formalization draft credit. Metadata truthfully says statements only, with no author endorsement, completed formal proof, final review or Linux verification. No claim is made about ordered spectral intervals or Krylov convergence itself. Comparator lists all ten exports, no definition substitutions, and precisely the standard three allowed axioms.

The author/coordinator’s complete Challenge build log ends successfully (8708 jobs), with precisely ten deliberate placeholder warnings. I matched its receipt to the current mathematical files. This is an inspected coordinator run, not my independent Lean re-elaboration. No completed LeanCert proof, axiom audit or isolated Linux Comparator result is claimed. There are no statement blockers; proof completion and subsequent independent final review remain required.

## Exact reviewed bytes

The complete machine-readable hash roster, source Git verification, diagnostic exit result and inspected build provenance are in `referee-1-statement-checks.json`. Material boundary hashes:

| File | SHA-256 |
|---|---|
'''
for f in ['NLA/KE05/Definitions.lean','Challenge.lean','NUMERICAL_TARGETS.md','formalization.yaml','comparator.json','SOURCE_PROVENANCE.json']:
 body+=f'| `{f}` | `{inputs[f]}` |\n'
(p/'reviews/statement-referee-1.md').write_text(body)
print(json.dumps({'verdict':'APPROVE','report_sha256':h((p/'reviews/statement-referee-1.md').read_bytes()),'checks_sha256':h((p/'reviews/referee-1-statement-checks.json').read_bytes())},indent=2))
