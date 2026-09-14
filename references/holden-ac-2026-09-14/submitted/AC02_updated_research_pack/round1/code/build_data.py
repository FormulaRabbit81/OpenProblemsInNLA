#!/usr/bin/env python3
"""Reconstruct two attributed rank-23 schemes from explicit scalar forms.

Laderman: Bull. AMS 82 (1976), 126-128.
Sun: arXiv:2604.27645v1 (2026), Section 5. These are not new algorithms.
Row-major coordinates throughout. Output W rows correspond to products.
"""
from pathlib import Path
import json
import re

ROOT = Path(__file__).resolve().parents[1]

def linear(expression: str, letter: str, size: int) -> list[int]:
    """Parse sums of signed a11/b11 or p1 variables, without evaluating code."""
    s = expression.replace(' ', '')
    if not s or s[0] not in '+-':
        s = '+' + s
    terms = re.findall(r'([+-])(' + re.escape(letter) + r'\d+)', s)
    if ''.join(sign + token for sign, token in terms) != s:
        raise ValueError(f'Invalid linear form: {expression}')
    out = [0] * size
    for sign, token in terms:
        num = token[len(letter):]
        if letter in ('a', 'b'):
            if len(num) != 2 or any(c not in '123' for c in num):
                raise ValueError(token)
            index = 3 * (int(num[0]) - 1) + int(num[1]) - 1
        else:
            index = int(num) - 1
        if not 0 <= index < size:
            raise ValueError(token)
        out[index] += 1 if sign == '+' else -1
    return out

LADERMAN_U = [
'a11+a12+a13-a21-a22-a32-a33', 'a11-a21', 'a22', '-a11+a21+a22',
'a21+a22','a11','-a11+a31+a32','-a11+a31','a31+a32',
'a11+a12+a13-a22-a23-a31-a32','a32','-a13+a32+a33','a13-a33','a13',
'a32+a33','-a13+a22+a23','a13-a23','a22+a23','a12','a23','a21','a31','a33']
LADERMAN_V = [
'b22','-b12+b22','-b11+b12+b21-b22-b23-b31+b33','b11-b12+b22',
'-b11+b12','b11','b11-b13+b23','b13-b23','-b11+b13','b23',
'-b11+b13+b21-b22-b23-b31+b32','b22+b31-b32','b22-b32','b31',
'-b31+b32','b23+b31-b33','b23-b33','-b31+b33','b21','b32','b13','b12','b33']
LADERMAN_C = [
'p6+p14+p19','p1+p4+p5+p6+p12+p14+p15','p6+p7+p9+p10+p14+p16+p18',
'p2+p3+p4+p6+p14+p16+p17','p2+p4+p5+p6+p20','p14+p16+p17+p18+p21',
'p6+p7+p8+p11+p12+p13+p14','p12+p13+p14+p15+p22','p6+p7+p8+p9+p23']
SUN_U = [
'a22+a32+a33','a21-a22-a23+a31-a32','a23','a12+a13-a22-a32-a33',
'a12-a22-a32-a33','a22','a33','-a22+a31-a32','a22','a12-a22+a31-a32',
'-a12+a22+a32','a33','a11-a12+a22-a31+a32','a13','a12','a31',
'a11-a12-a21+a22-a31+a32','a11','a23','a21',
'-a11+a12+a13+a21-a22-a23+a31-a32','a31-a32',
'a11-a12-a21+a22+a23-a31+a32']
SUN_V = [
'-b11+b12+b13-b21+b22+b23','-b11+b12+b13','-b11+b12+b13+b32+b33','b33',
'-b11+b12+b13-b21+b22+b23-b33','b23','b32','-b11+b12+b13+b22','b21',
'b11-b12-b22','b13+b23-b33','-b11+b12+b13-b21+b22+b23+b31-b33','b13',
'b31','b21','b12+b22','b11-b12-b32','b11','b31','b11','b32','b22',
'b11-b12-b13-b32']
SUN_C = [
'p14+p15+p18','p2-p8-p10-p13+p18+p21-p23','p1+p4+p5+p8+p10+p13+p15',
'p9+p19+p20','p2-p8-p13+p17+p20+p22-p23','p3+p6+p13-p17+p23',
'p5-p9+p10+p11+p12+p15+p16','p7+p16-p22','p1+p5-p6+p8+p10+p11+p15']

def build(name: str, us: list[str], vs: list[str], cs: list[str], source: str) -> dict:
    assert len(us) == len(vs) == 23 and len(cs) == 9
    ct = [linear(c, 'p', 23) for c in cs]
    return {'name': name, 'source': source, 'coordinate_order': 'row-major, 0-based',
            'U': [linear(x,'a',9) for x in us], 'V': [linear(x,'b',9) for x in vs],
            'W': [[ct[k][t] for k in range(9)] for t in range(23)]}

if __name__ == '__main__':
    for name, args in [('laderman23', (LADERMAN_U,LADERMAN_V,LADERMAN_C,
        'Julian D. Laderman, Bull. AMS 82 (1976), 126-128; doi:10.1090/S0002-9904-1976-13988-2')),
        ('sun23',(SUN_U,SUN_V,SUN_C,'Yinqi Sun, arXiv:2604.27645v1, Section 5 (CC BY 4.0)'))]:
        path = ROOT/'data'/f'{name}.json'
        path.write_text(json.dumps(build(name,*args),indent=2)+'\n')
        print(path)
