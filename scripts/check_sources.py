#!/usr/bin/env python3
"""Validate source inventories, closure membership, and frozen verification bindings."""
import hashlib
import json
from pathlib import Path

from verify_formalizations import inspect_source_closure

ROOT = Path(__file__).resolve().parents[1]


def check_verification_binding(item, result):
    fingerprint = hashlib.sha256(json.dumps(item['files'], sort_keys=True).encode()).hexdigest()
    if result.get('source_tree_sha256') != fingerprint:
        raise ValueError(f'{item["id"]}: verification status does not match source inventory')
    if result.get('compiled') is True:
        if result.get('axiom_inspection_exit_code') != 0:
            raise ValueError(f'{item["id"]}: missing successful dependency inspection')
    elif (result.get('compiled') is None and result.get('verification_status') == 'not_checked'
          and item.get('verification_status') == 'not_checked'
          and item.get('validation') == 'source_inventory_checked'):
        unknown_fields = ['axiom_inspection_exit_code', 'theorems_checked', 'algorithm_theorems_checked',
                          'nonstandard_dependencies', 'algorithm_nonstandard_dependencies',
                          'algorithm_uses_sorryAx', 'public_algorithm_nonstandard_dependencies',
                          'public_algorithm_uses_sorryAx', 'algorithm_native_decide_axioms',
                          'algorithm_custom_axioms', 'elapsed_seconds']
        if any(result.get(field) is not None for field in unknown_fields):
            raise ValueError(f'{item["id"]}: unchecked source has asserted verification results')
        if result.get('source_holes') != item.get('local_holes'):
            raise ValueError(f'{item["id"]}: source-hole inventory mismatch')
    else:
        raise ValueError(f'{item["id"]}: invalid verification status')


def check_inventory(relative, *, verified):
    directory = ROOT / relative
    manifest = json.loads((directory / 'manifest.json').read_text())
    records = {}
    if verified:
        report = json.loads((directory / 'VERIFICATION.json').read_text())
        records = {r['id']: r for r in report['algorithms']}
        if set(records) != {a['id'] for a in manifest['algorithms']}:
            raise ValueError(f'{relative}: verification inventory differs from sources')
    for item in manifest['algorithms']:
        project = directory / item['directory']
        if not project.resolve().is_relative_to(directory.resolve()):
            raise ValueError('Project path escapes its inventory')
        for name, metadata in {**item['files'], **{r['path']: r for r in item['source_inputs']}}.items():
            path = project / name
            if not path.resolve().is_relative_to(project.resolve()) or not path.is_file():
                raise ValueError(f'{relative}/{item["id"]}: invalid source path {name}')
            if hashlib.sha256(path.read_bytes()).hexdigest() != metadata['sha256']:
                raise ValueError(f'{relative}/{item["id"]}: source hash changed: {name}')
        inspect_source_closure(project, item)
        actual = {str(p.relative_to(project)) for p in project.rglob('*.lean')
                  if p.name != 'lakefile.lean' and '.lake' not in p.relative_to(project).parts}
        if actual != set(item['files']):
            raise ValueError(f'{relative}/{item["id"]}: unlisted or missing Lean sources')
        if verified:
            check_verification_binding(item, records[item['id']])
    return len(manifest['algorithms'])


def main():
    for directory in ['formalizations', 'soptlib']:
        count = check_inventory(directory, verified=True)
        records = json.loads((ROOT / directory / 'VERIFICATION.json').read_text())['algorithms']
        compiled = sum(record['compiled'] is True for record in records)
        print(f'{directory}: {count} source inventories match; '
              f'{compiled} successful verification records; {count - compiled} unchecked')


if __name__ == '__main__':
    main()
