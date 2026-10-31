import hashlib
from pathlib import Path
import subprocess
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

import verify_formalizations as verifier


class CompileOptionsTest(unittest.TestCase):
    def test_options_reach_compiler_and_invalidate_cached_module(self):
        with tempfile.TemporaryDirectory() as temporary:
            root = Path(temporary)
            project = root / 'formalizations' / 'Test'
            source = project / 'Algorithms' / 'Test.lean'
            source.parent.mkdir(parents=True)
            source.write_text('theorem test : True := True.intro\n')
            (project / 'lake-manifest.json').write_text('{}')
            metadata = {'sha256': hashlib.sha256(source.read_bytes()).hexdigest()}
            item = {'id': 'Test', 'directory': 'Test', 'entry': 'Algorithms/Test.lean',
                    'lean_toolchain': 'leanprover/lean4:v4.29.0',
                    'files': {'Algorithms/Test.lean': metadata}}
            args = SimpleNamespace(manifest=root / 'formalizations/manifest.json',
                                   cache=root / 'cache', threads=2, memory_mb=16000, timeout=30)
            commands = []

            def run(command, **kwargs):
                if '-o' in command:
                    commands.append(command)
                    Path(command[command.index('-o') + 1]).write_bytes(b'test object')
                return subprocess.CompletedProcess(command, 0)

            rows = [{'declaration': 'test', 'module': 'Algorithms.Test',
                     'algorithm': True, 'axioms': []}]
            with patch.object(verifier, 'ROOT', root), \
                 patch.object(verifier.subprocess, 'run', side_effect=run), \
                 patch.object(verifier, 'read_axiom_graph', return_value=rows):
                first = verifier.verify_one(item, args, root, [])
                second = verifier.verify_one(item, args, root, [])
                self.assertTrue(first['compiled'] and second['compiled'])
                self.assertEqual(len(commands), 1)
                self.assertFalse(any(a.startswith('-D') for a in commands[0]))
                metadata['lean_options'] = {'maxHeartbeats': 1000000}
                third = verifier.verify_one(item, args, root, [])
                fourth = verifier.verify_one(item, args, root, [])
                self.assertTrue(third['compiled'] and fourth['compiled'])
                self.assertEqual(len(commands), 2)
                self.assertIn('-DmaxHeartbeats=1000000', commands[-1])
                metadata['lean_options'] = {'maxHeartbeats': 200000}
                fifth = verifier.verify_one(item, args, root, [])
                self.assertTrue(fifth['compiled'])
                self.assertEqual(len(commands), 3)
                self.assertIn('-DmaxHeartbeats=200000', commands[-1])


if __name__ == '__main__':
    unittest.main()
