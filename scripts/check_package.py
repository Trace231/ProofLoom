#!/usr/bin/env python3
"""Check the source release offline, without model calls or dependency installs."""

from pathlib import Path

from check_sources import main as check_sources

ROOT = Path(__file__).resolve().parents[1]


def main():
    for name in ("engine", ".env.example", "requirements.lock.txt"):
        if (ROOT / name).exists():
            raise ValueError(f"Unexpected generation component in artifact release: {name}")
    check_sources()
    print("Artifact checks passed. No Lean build was performed.")


if __name__ == "__main__":
    main()
