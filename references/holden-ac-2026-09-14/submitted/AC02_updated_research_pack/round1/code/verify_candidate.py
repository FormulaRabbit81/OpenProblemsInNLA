#!/usr/bin/env python3
"""Verify a 3x3 multiplication identity over Q(i), in exact arithmetic.

JSON contains U,V,W, each an r-by-9 row-major array. Entries may be integers,
rational strings, or {"re": "p/q", "im": "s/t"}. Floats are rejected. A pass
proves an identity with at most r nonzero products, never its optimality.
No NumPy or symbolic algebra package is needed by this checker.
"""
from __future__ import annotations
from dataclasses import dataclass
from fractions import Fraction
from pathlib import Path
from typing import Any
import argparse
import json

@dataclass(frozen=True)
class QComplex:
    re: Fraction = Fraction(0)
    im: Fraction = Fraction(0)
    def __add__(self, other: 'QComplex') -> 'QComplex':
        return QComplex(self.re+other.re,self.im+other.im)
    def __mul__(self, other: 'QComplex') -> 'QComplex':
        return QComplex(self.re*other.re-self.im*other.im,
                        self.re*other.im+self.im*other.re)
    def __bool__(self) -> bool:
        return bool(self.re or self.im)
    def json_value(self) -> str | dict[str,str]:
        if not self.im: return str(self.re)
        return {'re':str(self.re),'im':str(self.im)}

def rational(x: Any) -> Fraction:
    if isinstance(x,bool) or not isinstance(x,(int,str)):
        raise ValueError('Exact rational coefficients must be integers or strings, not floats.')
    return Fraction(x)

def coefficient(x: Any) -> QComplex:
    if isinstance(x,dict):
        if set(x) != {'re','im'}:
            raise ValueError('A complex entry must contain exactly re and im.')
        return QComplex(rational(x['re']),rational(x['im']))
    return QComplex(rational(x))

def verify_object(obj: dict[str,Any]) -> dict[str,Any]:
    blocks=[];r=None
    for name in ('U','V','W'):
        raw=obj[name]
        if not isinstance(raw,list) or not raw:
            raise ValueError(f'{name} must be a nonempty list of rows.')
        if r is None:r=len(raw)
        if len(raw)!=r or any(not isinstance(row,list) or len(row)!=9 for row in raw):
            raise ValueError('U,V,W must have the same shape (r,9).')
        blocks.append([[coefficient(v) for v in row] for row in raw])
    u,v,w=blocks
    failures=[];zero=QComplex()
    # This loop uses six matrix indices directly, not common.target().
    for i in range(3):
        for j in range(3):
            for jp in range(3):
                for k in range(3):
                    for ip in range(3):
                        for kp in range(3):
                            actual=zero
                            for t in range(r):
                                actual=actual+u[t][3*i+j]*v[t][3*jp+k]*w[t][3*ip+kp]
                            expected=QComplex(Fraction(int(i==ip and j==jp and k==kp)))
                            if actual!=expected:
                                failures.append({'indices':[i,j,jp,k,ip,kp],
                                    'actual':actual.json_value(),'expected':expected.json_value()})
    nonzero=sum(bool(any(u[t])) and bool(any(v[t])) and bool(any(w[t])) for t in range(r))
    return {'field':'Q(i)','identities_checked':729,'slots':r,
            'nonzero_products':nonzero,'identity_verified':not failures,
            'failed_identities':len(failures),'first_failures':failures[:10],
            'optimal_rank_certified':False}

def main() -> int:
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('candidate',type=Path)
    args=p.parse_args()
    try:
        result=verify_object(json.loads(args.candidate.read_text()))
    except (ValueError,KeyError,TypeError,OSError,ZeroDivisionError) as exc:
        print(json.dumps({'error':str(exc)}));return 2
    print(json.dumps(result,indent=2))
    return 0 if result['identity_verified'] else 1

if __name__=='__main__': raise SystemExit(main())
