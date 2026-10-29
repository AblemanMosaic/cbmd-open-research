"""Boundary, refusal, and falsification tests for the public reference API."""

from __future__ import annotations

import json
from pathlib import Path
import subprocess
import sys
import unittest

from cbmd_reference import (BCM1Counts, UniversalState, joint_entry, master_numerator,
                            orbit_compatible, swap_positions)
from cbmd_reference.oracle import (formula_oracle, integer_choose, interpolation_oracle,
                                   native_entry_oracle, orbit_oracle, parity_coefficients)


class ScalarTests(unittest.TestCase):
    def test_negative_upper_binomial(self):
        self.assertEqual([integer_choose(-3, k) for k in range(5)], [1, -3, 6, -10, 15])

    def test_A_zero_is_not_skipped_by_meter(self):
        result = master_numerator(0, 3, 2, 0)
        self.assertEqual(result.negative_table, (1, 0, 0))
        self.assertEqual(result.counts, BCM1Counts(8, 4, 3))
        self.assertEqual(result.value, formula_oracle(0, 3, 2, 0))

    def test_R_one(self):
        for a in range(4):
            result = master_numerator(a, 1, 8, 0)
            self.assertEqual(result.value, (-1) ** a)
            self.assertEqual(result.counts, BCM1Counts(2, 0, 1))

    def test_m_zero_and_sign_regression(self):
        # The old unsigned/doubled-f-sign transport failed at this boundary.
        self.assertEqual(interpolation_oracle(0, 2, 1, 0), 2)
        self.assertEqual(master_numerator(0, 2, 2, 1).value, 2)
        self.assertEqual(parity_coefficients(0, 2), (1, -2))

    def test_refuses_unsupported_or_nonintegral_parameters(self):
        for parameters in ((0, 0, 0, 0), (0, 1, 0, 1), (-1, 2, 1, 0),
                           (0, 2, -1, 0), (True, 2, 1, 0), (1.0, 2, 1, 0)):
            with self.subTest(parameters=parameters), self.assertRaises(ValueError):
                master_numerator(*parameters)


class StateTests(unittest.TestCase):
    def setUp(self):
        self.u = UniversalState((0, 0, 1), ((1, 1, 1), (0, 1, 0)))

    def test_swap_and_orbit(self):
        y = swap_positions(0, (1,), self.u)
        self.assertTrue(orbit_compatible(0, self.u, y))
        self.assertTrue(orbit_oracle(0, self.u, y))
        self.assertEqual(swap_positions(0, (1,), y), self.u)

    def test_unselected_slot_is_required(self):
        y = UniversalState(self.u.head, (self.u.slots[0], (1, 1, 0)))
        self.assertFalse(orbit_compatible(0, self.u, y))
        self.assertEqual(joint_entry(0, 0, 1, 2, self.u, y).branch, "OUTSIDE_ORBIT")
        self.assertEqual(native_entry_oracle(0, 0, 1, 2, self.u, y), 0)

    def test_selected_slot_is_required(self):
        y = UniversalState(self.u.head, ((1, 0, 1), self.u.slots[1]))
        self.assertFalse(orbit_compatible(0, self.u, y))

    def test_support_boundary(self):
        live = joint_entry(0, 0, 1, 2, self.u, self.u)
        self.assertNotEqual(live.value, 0)
        self.assertEqual(live.value, native_entry_oracle(0, 0, 1, 2, self.u, self.u))
        rejected = joint_entry(0, 0, 1, 1, self.u, self.u)
        self.assertEqual((rejected.value, rejected.branch), (0, "ABOVE_MISMATCH_SUPPORT"))

    def test_three_color_case(self):
        u = UniversalState((0, 2), ((1, 0),), 3)
        y = swap_positions(0, (1,), u)
        self.assertTrue(orbit_compatible(0, u, y))
        self.assertEqual(joint_entry(0, 0, 1, 2, u, y).value,
                         native_entry_oracle(0, 0, 1, 2, u, y))

    def test_refuses_non_joint_and_invalid_shapes(self):
        with self.assertRaises(ValueError):
            joint_entry(0, 2, 1, 2, self.u, self.u)
        with self.assertRaises(ValueError):
            joint_entry(1, 0, 1, 2, self.u, self.u)
        with self.assertRaises(ValueError):
            swap_positions(0, (3,), self.u)
        with self.assertRaises(ValueError):
            swap_positions(0, (1, True), self.u)
        with self.assertRaises(ValueError):
            UniversalState((0,), ((1, 0),))
        with self.assertRaises(ValueError):
            UniversalState((0,), ((2,),))
        with self.assertRaises(ValueError):
            UniversalState((False,), ((1,),))


class CLITests(unittest.TestCase):
    def test_cli_values_vectors_and_refusal(self):
        script = Path(__file__).with_name("evaluate.py")
        result = subprocess.run([sys.executable, str(script), "1", "3", "4", "0"],
                                capture_output=True, text=True, check=True)
        output = json.loads(result.stdout)
        self.assertEqual(output["value"], formula_oracle(1, 3, 4, 0))
        self.assertEqual(output["counts"], {"mul": 8, "div": 4, "add": 3})
        self.assertEqual(len(output["choose_table"]), 3)
        bad = subprocess.run([sys.executable, str(script), "0", "0", "1", "0"],
                             capture_output=True, text=True)
        self.assertEqual(bad.returncode, 2)
        self.assertIn("R >= 1", bad.stderr)


if __name__ == "__main__":
    unittest.main()
