"""Check propagation, including a cyclic declaration graph and axiom types."""

import json
from pathlib import Path
import tempfile
import unittest
from verify_formalizations import read_axiom_graph


class DependencyGraphTests(unittest.TestCase):
    def test_transitive_cycle_and_axiom_type(self):
        roots = [
            {"declaration": n, "module": "Fixture", "algorithm": True}
            for n in ["clean", "left", "right", "conditional"]
        ]
        nodes = [
            ("clean", False, []),
            ("left", False, ["right"]),
            ("right", False, ["left", "sorryAx"]),
            ("sorryAx", True, []),
            ("conditional", False, ["custom"]),
            ("custom", True, ["Classical.choice"]),
            ("Classical.choice", True, []),
        ]
        with tempfile.TemporaryDirectory() as d:
            p = Path(d) / "graph.txt"
            p.write_text(
                "".join("PROOFLOOM_ROOT " + json.dumps(r) + "\n" for r in roots)
                + "".join(
                    "PROOFLOOM_NODE "
                    + json.dumps(dict(name=n, axiom=a, deps=deps))
                    + "\n"
                    for n, a, deps in nodes
                )
            )
            result = {r["declaration"]: r["axioms"] for r in read_axiom_graph(p)}
        self.assertEqual(
            result,
            {
                "clean": [],
                "left": ["sorryAx"],
                "right": ["sorryAx"],
                "conditional": ["Classical.choice", "custom"],
            },
        )


if __name__ == "__main__":
    unittest.main()
