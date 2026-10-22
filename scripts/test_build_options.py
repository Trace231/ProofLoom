import hashlib
import json
import unittest

from check_sources import check_verification_binding
from verify_formalizations import module_options


class BuildOptionsTests(unittest.TestCase):
    def test_library_options_do_not_leak_to_other_modules(self):
        item = {"lean_options_by_prefix": {"Algorithms": {"maxHeartbeats": 1000000}}}
        self.assertEqual(module_options(item, "Algorithms/Example/Part.lean"),
                         ["-DmaxHeartbeats=1000000"])
        self.assertEqual(module_options(item, "SOptLib/Model.lean"), [])
        self.assertEqual(module_options(item, "AlgorithmsOther/Example.lean"), [])
        self.assertEqual(module_options({}, "Algorithms/Example.lean"), [])

    def test_more_specific_options_override_parent(self):
        item = {"lean_options_by_prefix": {
            "Algorithms.Example": {"maxHeartbeats": 2000000},
            "Algorithms": {"maxHeartbeats": 1000000, "autoImplicit": False},
        }}
        self.assertEqual(module_options(item, "Algorithms/Example.lean"),
                         ["-DautoImplicit=false", "-DmaxHeartbeats=2000000"])

    def test_changed_options_cannot_reuse_old_verification_record(self):
        item = {"id": "example", "files": {},
                "lean_options_by_prefix": {"Algorithms": {"maxHeartbeats": 1000000}}}
        result = {"compiled": True, "axiom_inspection_exit_code": 0,
                  "source_tree_sha256": hashlib.sha256(json.dumps({}, sort_keys=True).encode()).hexdigest()}
        with self.assertRaisesRegex(ValueError, "build options"):
            check_verification_binding(item, result)
        result["lean_options_by_prefix"] = item["lean_options_by_prefix"]
        check_verification_binding(item, result)


if __name__ == "__main__":
    unittest.main()
