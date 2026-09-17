#!/usr/bin/env python3
"""Mutation checks for the release source/coverage audit; standard library only."""
import contextlib
import io
from pathlib import Path
import shutil
import tempfile

import audit_source as audit

ORIGINAL = audit.ROOT


def rejected(name, mutate):
    with tempfile.TemporaryDirectory(prefix="xz-source-audit-") as tmp:
        root = Path(tmp)
        shutil.copytree(ORIGINAL / audit.PROJECT, root / audit.PROJECT)
        for filename in (f"{audit.PROJECT}.lean", "README.md", "FORMALIZATION_STATUS.md",
                         "xz_mathieu_su2_counterexamples.tex"):
            shutil.copy2(ORIGINAL / filename, root / filename)
        mutate(root)
        audit.ROOT = root
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                audit.check_lean()
                audit.check_ledger()
        except ValueError:
            print(f"Rejected: {name}")
        else:
            raise AssertionError(f"Audit accepted invalid mutation: {name}")
        finally:
            audit.ROOT = ORIGINAL


def replace(root, filename, before, after):
    path = root / filename
    text = path.read_text()
    assert before in text
    path.write_text(text.replace(before, after, 1))


if __name__ == "__main__":
    rejected("proof placeholder", lambda r: (r / audit.PROJECT / "Basic.lean").open("a").write(
        "\ntheorem invalid : False := sorry\n"))
    rejected("unreachable module", lambda r: (r / audit.PROJECT / "Orphan.lean").write_text(
        "theorem unreachable : True := True.intro\n"))
    rejected("missing manuscript result", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "### `thm:su2`", "### `unlisted-result`"))
    rejected("cyclic dependency", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "- Dependencies: none.", "- Dependencies: `def:xz`."))
    rejected("unknown dependency", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "- Dependencies: none.", "- Dependencies: `absent` ."))
    rejected("missing proved declaration", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "`basic_xz`", "`absent_theorem`"))
    rejected("unproved core claim", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "- Status: **PROVED**.", "- Status: **TODO**."))
    rejected("downgraded mandatory core gate", lambda r: replace(r, "FORMALIZATION_STATUS.md",
        "- Core release gate: yes.", "- Core release gate: no."))
    rejected("false full-paper claim", lambda r: (r / "README.md").open("a").write(
        "\nThe paper is fully formalized.\n"))
    rejected("unlisted remaining claim", lambda r: replace(r, "README.md",
        "`rem:generating`", "generating-function discussion"))
    rejected("changed canonical manuscript", lambda r: (r / "xz_mathieu_su2_counterexamples.tex").open("a").write(
        "\n% changed\n"))
    print("All 11 audit mutation checks passed.")
