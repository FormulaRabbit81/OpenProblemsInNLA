#!/usr/bin/env python3
"""Regression and deliberately corrupted-certificate tests (not a formal proof)."""
import copy
import json
import unittest
from unittest.mock import patch
from common import ROOT,load_scheme
import verify
from verify_candidate import verify_object

class CertificateTests(unittest.TestCase):
    def baseline(self):
        return json.loads((ROOT/'data/laderman23.json').read_text())
    def test_rational_baseline(self):
        self.assertTrue(verify_object(self.baseline())['identity_verified'])
    def test_complex_slot_gauge(self):
        a=self.baseline()
        a['U'][0]=[{'re':'0','im':str(v)} for v in a['U'][0]]
        a['W'][0]=[{'re':'0','im':str(-v)} for v in a['W'][0]]
        self.assertTrue(verify_object(a)['identity_verified'])
    def test_corrupt_identity_is_rejected(self):
        a=self.baseline();a['U'][0][0]+=1
        self.assertFalse(verify_object(a)['identity_verified'])
    def test_float_input_is_rejected(self):
        a=self.baseline();a['U'][0][0]=1.0
        with self.assertRaises(ValueError):verify_object(a)
    def test_corrupt_forcing_trace_is_rejected(self):
        cert=verify.read('laderman23_forcing.json')
        cert['trace'][0]['new_variables']=[]
        with patch.object(verify,'read',return_value=cert):
            with self.assertRaises(AssertionError):verify.check_forcing('laderman23',load_scheme('laderman23'))
    def test_corrupt_laurent_certificate_is_rejected(self):
        cert=verify.read('laderman_torus.json');cert['final']['E'][0][0]+=1
        with patch.object(verify,'read',return_value=cert):
            with self.assertRaises(AssertionError):verify.check_torus(load_scheme('laderman23'))
    def test_six_parameter_example(self):
        a=json.loads((ROOT/'data/laderman_six_parameter_example.json').read_text())
        self.assertTrue(verify_object(a)['identity_verified'])

if __name__=='__main__':unittest.main(verbosity=2)
