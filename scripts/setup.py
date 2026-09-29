#!/usr/bin/env python3
"""Install pinned public dependencies into this checkout (Linux, Python 3.11+)."""

import argparse, json, os, shutil, subprocess, sys, urllib.request
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEPS = ROOT / ".deps"


def run(args, cwd=None, env=None):
    print("+ " + " ".join(map(str, args)), flush=True)
    subprocess.run(list(map(str, args)), cwd=cwd, env=env, check=True)


def git_revision(path):
    return subprocess.check_output(
        ["git", "-C", str(path), "rev-parse", "HEAD"], text=True
    ).strip()


def checkout(url, rev, path):
    if not path.exists():
        path.parent.mkdir(parents=True, exist_ok=True)
        run(["git", "init", path])
        run(["git", "-C", path, "remote", "add", "origin", url])
        run(["git", "-C", path, "fetch", "--depth", "1", "origin", rev])
        run(["git", "-C", path, "checkout", "--detach", "FETCH_HEAD"])
    if git_revision(path) != rev:
        raise RuntimeError(
            f"{path}: checkout differs from the required revision; use a separate dependency directory"
        )


def link(target, path):
    if path.is_symlink():
        if path.resolve() == target.resolve():
            return
        raise RuntimeError(f"Refusing to replace existing link: {path}")
    if path.exists():
        raise RuntimeError(f"Refusing to replace existing directory: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    path.symlink_to(target.resolve(), target_is_directory=True)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mode", choices=["proofs"], default="proofs")
    p.add_argument(
        "--packages",
        type=Path,
        help="Reuse an existing exact-revision dependency cache",
    )
    a = p.parse_args()
    if sys.version_info < (3, 11):
        p.error("Python 3.11 or newer is required")
    if not shutil.which("git"):
        p.error("Install git first")
    DEPS.mkdir(exist_ok=True)
    env = os.environ.copy()
    env["PATH"] = str(Path.home() / ".elan/bin") + os.pathsep + env.get("PATH", "")
    if not shutil.which("elan", path=env["PATH"]):
        # Elan installs the toolchain named below; no rolling Lean version is selected.
        installer = DEPS / "elan-init.sh"
        urllib.request.urlretrieve(
            "https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh",
            installer,
        )
        run(
            ["sh", installer, "-y", "--no-modify-path", "--default-toolchain", "none"],
            env=env,
        )
    installed = subprocess.check_output(
        ["elan", "toolchain", "list"], env=env, text=True
    )
    if "leanprover/lean4:v4.29.0" not in {
        line.split()[0] for line in installed.splitlines() if line.strip()
    }:
        run(["elan", "toolchain", "install", "leanprover/lean4:v4.29.0"], env=env)
    lock = json.loads((ROOT / "soptlib/lake-manifest.json").read_text())
    packages = DEPS / "packages"
    if a.packages:
        link(a.packages, packages)
    packages.mkdir(exist_ok=True)
    for item in lock["packages"]:
        checkout(item["url"], item["rev"], packages / item["name"])
    project = DEPS / "lean"
    project.mkdir(exist_ok=True)
    for name in ["lean-toolchain", "lake-manifest.json"]:
        shutil.copyfile(ROOT / "soptlib" / name, project / name)
    (project / "lakefile.lean").write_text(
        'import Lake\nopen Lake DSL\npackage proofloom_dependencies\nrequire mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "stable"\n'
    )
    link(packages, project / ".lake/packages")
    manifest = json.loads((ROOT / "formalizations/manifest.json").read_text())
    modules = sorted(
        {
            name
            for item in manifest["algorithms"]
            for name in item["external_imports"]
            if name.startswith("Mathlib")
        }
    )
    from verify_formalizations import import_names

    for source in (ROOT / "soptlib/SOptLib").rglob("*.lean"):
        modules.extend(
            name for name in import_names(source) if name.startswith("Mathlib")
        )
    modules.extend(["Mathlib.Data.Real.Basic", "Mathlib.Tactic"])
    for attempt in range(3):
        try:
            run(
                ["lake", "exe", "cache", "get", *sorted(set(modules))],
                cwd=project,
                env=env,
            )
            break
        except subprocess.CalledProcessError:
            if attempt == 2:
                raise

    (DEPS / "proofs.ready").write_text("leanprover/lean4:v4.29.0\n")
    print("Lean dependencies are ready.")


if __name__ == "__main__":
    try:
        main()
    except (OSError, RuntimeError, subprocess.CalledProcessError) as exc:
        raise SystemExit(str(exc))
