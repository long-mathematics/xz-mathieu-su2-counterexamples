#!/usr/bin/env python3
"""Fetch the pinned Mathlib cache for this project's direct Mathlib imports.

Passing the project root to Mathlib's cache tool does not traverse project-owned
imports. Enumerating direct Mathlib imports fetches their transitive dependencies
without downloading all of Mathlib or caching this project's proofs.
"""

import os
import re
import subprocess

from audit_source import PROJECT, ROOT, lean_code


if __name__ == "__main__":
    paths = [ROOT / f"{PROJECT}.lean", *sorted((ROOT / PROJECT).rglob("*.lean"))]
    modules = sorted({module for path in paths for module in re.findall(
        r"^\s*import\s+(Mathlib(?:\.[A-Za-z0-9_]+)+)\s*$",
        lean_code(path.read_text()), re.M)})
    if not modules:
        raise SystemExit("No direct Mathlib imports found")
    print(f"Fetching cache for {len(modules)} direct Mathlib imports and their dependencies.",
          flush=True)
    subprocess.run(["lake", "exe", "cache", "get", *modules], cwd=ROOT, check=True,
                   env={**os.environ, "MATHLIB_NO_CACHE_ON_UPDATE": "1"})
