#!/usr/bin/env python3
"""Compile the packaged source closures and inspect their theorem dependencies.

Only Mathlib's pinned dependency cache may be reused. Project source modules are
compiled into a content-addressed cache keyed by their complete local imports.
No model, pipeline run, historical log, or machine-local project is required.
"""

from __future__ import annotations

import argparse
from concurrent.futures import ThreadPoolExecutor
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
BASE_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}


def sha(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def mask(text: str) -> str:
    out = []
    i = 0
    depth = 0
    string = False
    while i < len(text):
        c = text[i]
        if depth:
            if text.startswith("/-", i):
                depth += 1
                out.extend("  ")
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif string:
            if c == "\\" and i + 1 < len(text):
                out.extend("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
                if c == '"':
                    string = False
        elif text.startswith("/-", i):
            depth = 1
            out.extend("  ")
            i += 2
        elif text.startswith("--", i):
            end = text.find("\n", i)
            end = len(text) if end < 0 else end
            out.extend(" " * (end - i))
            i = end
        elif c == '"':
            string = True
            out.append(" ")
            i += 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def import_names(path: Path) -> list[str]:
    names = []
    for line in mask(path.read_text()).splitlines():
        m = re.match(r"^\s*(?:(?:public|private|meta)\s+)?import\s+(.+)$", line)
        if m:
            names.extend(m.group(1).split())
    return names


def atomic_json(path, obj):
    path.parent.mkdir(parents=True, exist_ok=True)
    tmp = path.with_suffix(".tmp")
    tmp.write_text(json.dumps(obj, indent=2) + "\n")
    tmp.replace(path)


def dependency_paths(packages: Path, lock: dict) -> list[str]:
    paths = []
    for package in lock["packages"]:
        path = packages / package["name"]
        if not path.is_dir():
            raise RuntimeError(f"Missing dependency: {path}; run setup first")
        commit = subprocess.run(
            ["git", "-C", str(path), "rev-parse", "HEAD"],
            capture_output=True,
            text=True,
        )
        if commit.returncode or commit.stdout.strip() != package["rev"]:
            raise RuntimeError(
                f'Dependency revision differs from lock: {package["name"]}'
            )
        paths.append(str(path / ".lake/build/lib/lean"))
    return paths


def inspect_source_closure(directory: Path, item: dict):
    ordered = []
    active = set()
    visited = set()

    def visit(relative):
        if relative in visited:
            return
        if relative in active:
            raise RuntimeError(f"Import cycle: {relative}")
        path = directory / relative
        if sha(path.read_bytes()) != item["files"][relative]["sha256"]:
            raise RuntimeError(f'Source differs from manifest: {item["id"]}/{relative}')
        active.add(relative)
        for module in import_names(path):
            child = module.replace(".", "/") + ".lean"
            if child in item["files"]:
                visit(child)
        active.remove(relative)
        visited.add(relative)
        ordered.append(relative)

    visit(item["entry"])
    if visited != set(item["files"]):
        raise RuntimeError("Manifest has unreachable local modules")
    return ordered


def audit_program(
    entry: str, local_modules: list[str], algorithm_modules: list[str]
) -> str:
    # Extract the same kernel declaration edges visited by Lean.collectAxioms.
    # Solve transitive reachability once in Python, sharing work across theorems.
    modules = ", ".join('"' + n + '"' for n in local_modules)
    algorithms = ", ".join('"' + n + '"' for n in algorithm_modules)
    return f"""import {entry}
import Lean
open Lean Elab Command
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  let localNames : Array String := #[{modules}]
  let algorithmNames : Array String := #[{algorithms}]
  let mut pending : Array Name := #[]
  for (name, info) in env.constants do
    if let .thmInfo _ := info then
      if let some idx := env.getModuleIdxFor? name then
        let moduleName := env.header.moduleNames[idx.toNat]!
        if localNames.contains moduleName.toString then
          pending := pending.push name
          let row := Json.mkObj [
            ("declaration", Json.str name.toString),
            ("module", Json.str moduleName.toString),
            ("algorithm", Json.bool (algorithmNames.contains moduleName.toString))]
          logInfo ("PROOFLOOM_ROOT " ++ row.compress)
  let mut visited : NameSet := {{}}
  while !pending.isEmpty do
    let name := pending.back!
    pending := pending.pop
    if visited.contains name then continue
    visited := visited.insert name
    let mut deps : Array Name := #[]
    let mut isAxiom := false
    if let some info := env.checked.get.find? name then
      match info with
      | .axiomInfo v =>
        isAxiom := true
        deps := v.type.getUsedConstants
      | .defnInfo v => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
      | .thmInfo v => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
      | .opaqueInfo v => deps := v.type.getUsedConstants ++ v.value.getUsedConstants
      | .ctorInfo v => deps := v.type.getUsedConstants
      | .recInfo v => deps := v.type.getUsedConstants
      | .inductInfo v => deps := v.type.getUsedConstants ++ v.ctors.toArray
      | .quotInfo _ => pure ()
    pending := pending ++ deps
    let row := Json.mkObj [
      ("name", Json.str name.toString), ("axiom", Json.bool isAxiom),
      ("deps", Json.arr (deps.map (fun n => Json.str n.toString)))]
    logInfo ("PROOFLOOM_NODE " ++ row.compress)
"""


def read_axiom_graph(path):
    from collections import defaultdict, deque

    roots = []
    reverse = defaultdict(set)
    dependencies = defaultdict(set)
    queue = deque()
    with path.open() as source:
        for line in source:
            if "PROOFLOOM_ROOT " in line:
                roots.append(json.loads(line.split("PROOFLOOM_ROOT ", 1)[1]))
            elif "PROOFLOOM_NODE " in line:
                node = json.loads(line.split("PROOFLOOM_NODE ", 1)[1])
                name = node["name"]
                for dependency in node["deps"]:
                    reverse[dependency].add(name)
                if node["axiom"]:
                    dependencies[name].add(name)
                    queue.append(name)
    queued = set(queue)
    while queue:
        name = queue.popleft()
        queued.discard(name)
        for consumer in reverse[name]:
            new = dependencies[name] - dependencies[consumer]
            if new:
                dependencies[consumer].update(new)
                if consumer not in queued:
                    queue.append(consumer)
                    queued.add(consumer)
    for row in roots:
        row["axioms"] = sorted(dependencies[row["declaration"]])
    return roots


def verify_one(item, args, packages, deps):
    started = time.monotonic()
    directory = args.manifest.parent / item["directory"]
    result = {
        "id": item["id"],
        "compiled": False,
        "source_files": len(item["files"]),
        "modules": [],
    }
    build = ROOT / ".build" / args.manifest.parent.name / item["id"]
    build.mkdir(parents=True, exist_ok=True)
    local_lib = build / "lib"
    local_lib.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["LEAN_PATH"] = os.pathsep.join([str(local_lib), *deps])
    lean = [
        "elan",
        "run",
        item["lean_toolchain"],
        "lean",
        "-j",
        str(args.threads),
        "-M",
        str(args.memory_mb),
    ]
    fingerprints = {}
    lock_hash = sha((directory / "lake-manifest.json").read_bytes())
    try:
        ordered = inspect_source_closure(directory, item)
        for relative in ordered:
            source = directory / relative
            local_dependencies = [
                n.replace(".", "/") + ".lean"
                for n in import_names(source)
                if n.replace(".", "/") + ".lean" in item["files"]
            ]
            fingerprint = sha(
                json.dumps(
                    [
                        relative,
                        item["files"][relative]["sha256"],
                        item["lean_toolchain"],
                        lock_hash,
                        [(d, fingerprints[d]) for d in local_dependencies],
                    ],
                    sort_keys=True,
                ).encode()
            )
            fingerprints[relative] = fingerprint
            cache = args.cache / fingerprint
            cache.mkdir(parents=True, exist_ok=True)
            module_stem = Path(relative).stem
            object_path = cache / (module_stem + ".olean")
            with (cache / "lock").open("w") as handle:
                fcntl.flock(handle, fcntl.LOCK_EX)
                reused = (cache / "complete.json").is_file() and object_path.is_file()
                if not reused:
                    print(f'[{item["id"]}] compiling {relative}', flush=True)
                    with (cache / "compiler.log").open("w") as output:
                        proc = subprocess.run(
                            [*lean, "-o", str(object_path), relative],
                            cwd=directory,
                            env=env,
                            stdout=output,
                            stderr=subprocess.STDOUT,
                            timeout=args.timeout,
                        )
                    if proc.returncode:
                        result.update(
                            failed_module=relative,
                            exit_code=proc.returncode,
                            diagnostic=(cache / "compiler.log").read_text()[-8000:],
                        )
                        raise RuntimeError(f"Lean rejected {relative}")
                    atomic_json(
                        cache / "complete.json",
                        {
                            "source_sha256": item["files"][relative]["sha256"],
                            "fingerprint": fingerprint,
                        },
                    )
                destination = local_lib / Path(relative).with_suffix(".olean")
                destination.parent.mkdir(parents=True, exist_ok=True)
                for generated in cache.glob(module_stem + ".olean*"):
                    target = destination.parent / generated.name
                    if target.exists():
                        target.unlink()
                    try:
                        os.link(generated, target)
                    except OSError:
                        shutil.copy2(generated, target)
            result["modules"].append(
                {"path": relative, "cache_reused": reused, "fingerprint": fingerprint}
            )
        result["compiled"] = True
        module_names = [p[:-5].replace("/", ".") for p in ordered]
        algorithm_names = [
            p[:-5].replace("/", ".")
            for p in ordered
            if p.startswith("Algorithms/") and "/Analysis/" not in p
        ]
        audit = build / "CheckAxioms.lean"
        audit.write_text(
            audit_program(
                item["entry"][:-5].replace("/", "."), module_names, algorithm_names
            )
        )
        with (build / "axioms.log").open("w") as output:
            proc = subprocess.run(
                [*lean, str(audit)],
                cwd=directory,
                env=env,
                stdout=output,
                stderr=subprocess.STDOUT,
                timeout=args.timeout,
            )
        result["axiom_inspection_exit_code"] = proc.returncode
        if proc.returncode:
            result["axiom_inspection_error"] = (build / "axioms.log").read_text()[
                -4000:
            ]
        else:
            rows = read_axiom_graph(build / "axioms.log")
            result["theorems_checked"] = len(rows)
            result["algorithm_theorems_checked"] = sum(r["algorithm"] for r in rows)
            result["nonstandard_dependencies"] = [
                r for r in rows if set(r["axioms"]) - BASE_AXIOMS
            ]
            result["algorithm_nonstandard_dependencies"] = [
                r for r in result["nonstandard_dependencies"] if r["algorithm"]
            ]
            result["algorithm_uses_sorryAx"] = any(
                "sorryAx" in r["axioms"] for r in rows if r["algorithm"]
            )
            public_rows = [
                r
                for r in rows
                if r["algorithm"] and not r["declaration"].startswith("_private.")
            ]
            result["public_algorithm_nonstandard_dependencies"] = [
                r for r in public_rows if set(r["axioms"]) - BASE_AXIOMS
            ]
            result["public_algorithm_uses_sorryAx"] = any(
                "sorryAx" in r["axioms"] for r in public_rows
            )
            names = {
                name for r in rows if r["algorithm"] for name in r["axioms"]
            } - BASE_AXIOMS
            native_axioms = {
                name for name in names if "._native.native_decide.ax_" in name
            }
            result["algorithm_native_decide_axioms"] = sorted(native_axioms)
            result["algorithm_custom_axioms"] = sorted(
                names - native_axioms - {"sorryAx"}
            )
            if not rows:
                raise RuntimeError("Axiom inspection returned no theorem declarations")
    except (RuntimeError, OSError, subprocess.TimeoutExpired) as exc:
        result["error"] = str(exc)
    result["elapsed_seconds"] = round(time.monotonic() - started, 2)
    atomic_json(build / "result.json", result)
    print(
        f'[{item["id"]}] compiled={result["compiled"]}, axiom inspection={result.get("axiom_inspection_exit_code")}',
        flush=True,
    )
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--manifest", type=Path, default=ROOT / "formalizations/manifest.json",
        help="Source inventory; use soptlib/manifest.json to verify the full library",
    )
    parser.add_argument(
        "--algorithm",
        action="append",
        help="ID from formalizations/manifest.json; repeatable",
    )
    parser.add_argument("--packages", type=Path, default=ROOT / ".deps/packages")
    parser.add_argument("--cache", type=Path, default=ROOT / ".build/module_cache")
    parser.add_argument("--jobs", type=int, default=2)
    parser.add_argument("--threads", type=int, default=2)
    parser.add_argument("--memory-mb", type=int, default=16000)
    parser.add_argument(
        "--timeout", type=int, default=7200, help="Maximum seconds per module"
    )
    args = parser.parse_args()
    args.cache = args.cache.resolve()
    args.packages = args.packages.resolve()
    args.manifest = args.manifest.resolve()
    manifest = json.loads(args.manifest.read_text())
    selected = [
        a
        for a in manifest["algorithms"]
        if not args.algorithm or a["id"] in args.algorithm
    ]
    if not selected:
        parser.error("No matching algorithms")
    if args.algorithm and set(args.algorithm) - {a["id"] for a in selected}:
        parser.error("Unknown algorithm ID")
    lock = json.loads(
        (
            args.manifest.parent / selected[0]["directory"] / "lake-manifest.json"
        ).read_text()
    )
    dependencies = dependency_paths(args.packages, lock)
    for item in selected:
        other = json.loads(
            (
                args.manifest.parent / item["directory"] / "lake-manifest.json"
            ).read_text()
        )
        if [(p["name"], p["rev"]) for p in other["packages"]] != [
            (p["name"], p["rev"]) for p in lock["packages"]
        ]:
            parser.error(
                "Selected algorithms require different dependency versions; run them separately"
            )
    with ThreadPoolExecutor(max_workers=args.jobs) as executor:
        results = list(
            executor.map(
                lambda item: verify_one(item, args, args.packages, dependencies),
                selected,
            )
        )
    output = "verification.json" if args.manifest.parent.name == "formalizations" else args.manifest.parent.name + "_verification.json"
    atomic_json(ROOT / ".build" / output, {"algorithms": results})
    return (
        0
        if all(
            r["compiled"]
            and r.get("axiom_inspection_exit_code") == 0
            and "error" not in r
            for r in results
        )
        else 1
    )


if __name__ == "__main__":
    raise SystemExit(main())
