#!/usr/bin/env python3
"""Audit owned Lean source, root imports, and manuscript/ledger coverage.

This complements (and does not replace) Lean's kernel and audit_lean.lean.
Only the standard library is required. Dependencies under .lake are excluded.
"""

from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent.parent
PROJECT = "XZMathieuSU2Counterexamples"


def lean_code(source: str) -> str:
    """Remove nested block comments, line comments and escaped string literals."""
    result = []
    i = 0
    depth = 0
    quoted = False
    while i < len(source):
        pair = source[i:i + 2]
        if depth:
            if pair == "/-":
                depth += 1
                i += 2
            elif pair == "-/":
                depth -= 1
                i += 2
            else:
                result.append("\n" if source[i] == "\n" else " ")
                i += 1
        elif quoted:
            if source[i] == "\\":
                i += 2
            elif source[i] == '"':
                quoted = False
                i += 1
            else:
                i += 1
        elif pair == "/-":
            result.append(" ")
            depth = 1
            i += 2
        elif pair == "--":
            end = source.find("\n", i)
            i = len(source) if end == -1 else end
        elif source[i] == '"':
            result.append(" ")
            quoted = True
            i += 1
        else:
            result.append(source[i])
            i += 1
    if depth or quoted:
        raise ValueError("Unterminated Lean comment/string")
    return "".join(result)


def check_lean() -> None:
    # Include any future project-owned Lean files outside the library too.
    files = sorted(p for p in ROOT.rglob("*.lean")
                   if not any(part.startswith(".") for part in p.relative_to(ROOT).parts))
    code = {}
    forbidden = re.compile(r"\b(sorry|admit|axiom|unsafe|native_decide|implemented_by|extern)\b")
    for path in files:
        relative = path.relative_to(ROOT)
        body = lean_code(path.read_text())
        match = forbidden.search(body)
        if match:
            line = body[:match.start()].count("\n") + 1
            raise ValueError(f"Forbidden proof escape {match[0]}: {relative}:{line}")
        code[str(relative.with_suffix("")).replace("/", ".")] = body
    seen = set()

    def visit(module: str) -> None:
        if module in seen:
            return
        if module not in code:
            raise ValueError(f"Missing owned module: {module}")
        seen.add(module)
        for imported in re.findall(r"^\s*import\s+(\S+)", code[module], re.M):
            if imported == PROJECT or imported.startswith(PROJECT + "."):
                visit(imported)

    visit(PROJECT)
    owned = {name for name in code if name == PROJECT or name.startswith(PROJECT + ".")}
    if owned != seen:
        raise ValueError(f"Library modules absent from root imports: {sorted(owned - seen)}")
    print(f"Source audit: {len(files)} owned Lean files; {len(seen)} modules in root closure; no proof escapes.")


def check_ledger() -> None:
    ledger = (ROOT / "FORMALIZATION_STATUS.md").read_text()
    parts = re.split(r"^### `([^`]+)`\s*$", ledger, flags=re.M)
    entries = dict(zip(parts[1::2], parts[2::2]))
    if len(entries) != len(parts[1::2]):
        raise ValueError("Duplicate ledger identifiers")
    source = "\n".join(lean_code(p.read_text()) for p in (ROOT / PROJECT).rglob("*.lean"))
    declarations = set(re.findall(r"\b(?:theorem|lemma|def|abbrev|structure)\s+([\w.₀-₉]+)", source))
    graph = {}
    for name, body in entries.items():
        status = re.search(r"^- Status: \*\*([^*]+)\*\*", body, re.M)
        correspondence = re.search(r"^- Lean correspondence: `([^`]+)`", body, re.M)
        dependencies = re.search(r"^- Dependencies: (.*)$", body, re.M)
        if not status or status[1] not in {"PROVED", "PARTIAL", "TODO", "BLOCKED", "EXPOSITORY"} or not correspondence or not dependencies:
            raise ValueError(f"Incomplete ledger entry: {name}")
        for field in ("Statement", "Module", "Proof route / representation", "Blocker"):
            if not re.search(r"^- " + re.escape(field) + r": .+", body, re.M):
                raise ValueError(f"Missing {field} in {name}")
        if status[1] == "PROVED":
            for declaration in correspondence[1].split(", "):
                if declaration == "pending" or declaration.split(".")[-1] not in declarations:
                    raise ValueError(f"Proved entry {name} has no owned declaration: {declaration}")
        graph[name] = re.findall(r"`([^`]+)`", dependencies[1])
    done, active = set(), set()

    def visit(name: str) -> None:
        if name in active:
            raise ValueError(f"Circular ledger dependency: {name}")
        if name not in graph:
            raise ValueError(f"Unknown ledger dependency: {name}")
        if name in done:
            return
        active.add(name)
        for dependency in graph[name]:
            visit(dependency)
        active.remove(name)
        done.add(name)

    for name in graph:
        visit(name)
    tex = (ROOT / "xz_mathieu_su2_counterexamples.tex").read_text()
    canonical = re.search(r"Canonical manuscript Git blob: `([0-9a-f]{40})`", ledger)
    actual = subprocess.check_output(["git", "hash-object", "xz_mathieu_su2_counterexamples.tex"],
                                     cwd=ROOT, text=True).strip()
    if not canonical or actual != canonical[1]:
        raise ValueError("Canonical manuscript blob differs from the recorded source")
    all_labels = set(re.findall(r"\\label\{([^}]+)\}", tex))
    if all_labels - entries.keys():
        raise ValueError(f"Manuscript labels missing from ledger: {sorted(all_labels - entries.keys())}")
    required_core = {"def:mathieu", "eq:I-def", "eq:beta-binomial-intro", "eq:bernstein-average",
                     "eq:basic-f", "basic-spectrum", "eq:basic-moments", "thm:basic-xz",
                     "eq:family", "family-spectrum", "eq:family-pure", "eq:family-mixed",
                     "prop:family", "su2-coordinates", "eq:FG-family", "eq:su2-pure",
                     "eq:su2-mixed", "thm:su2", "small-pair"}
    if not required_core <= entries.keys() or any(
            "- Core release gate: yes." not in entries[k] for k in required_core):
        raise ValueError("Core release inventory cannot omit or downgrade mandatory obligations")
    # All current named environments are labelled; reject an unlabelled addition.
    results = re.findall(
        r"\\begin\{(theorem|lemma|corollary|proposition)\}(.*?)\\end\{\1\}",
        tex, re.S)
    labels = []
    for kind, body in results:
        label = re.search(r"\\label\{((?:thm|lem|cor|prop):[^}]+)\}", body)
        if not label or label[1] not in entries:
            raise ValueError(f"Named {kind} lacks a ledger counterpart: {body[:100]}")
        labels.append(label[1])
    ledger_named = {key for key in entries if key.startswith(("thm:", "lem:", "cor:", "prop:"))}
    if ledger_named != set(labels) or len(labels) != len(set(labels)):
        raise ValueError("Manuscript and ledger named-result inventories differ")
    readme = (ROOT / "README.md").read_text().lower()
    core = all("- Status: **PROVED**" in b for b in entries.values()
               if "- Core release gate: yes." in b)
    full = all("- Status: **PROVED**" in b or "- Status: **EXPOSITORY**" in b
               for b in entries.values())
    core_claim = "the core counterexample theorems are fully formalized in lean" in readme
    full_claim = "the paper is fully formalized" in readme
    if (core_claim and not core) or (full_claim and not full):
        raise ValueError("README completion claim exceeds proved ledger coverage")
    if "Release status: **CORE COMPLETE**" in ledger and not (core and core_claim):
        raise ValueError("Core release requires all core obligations and explicit README claim")
    if "Release status: **FULL COMPLETE**" in ledger and not (full and full_claim):
        raise ValueError("Full release requires all obligations and explicit README claim")
    if core_claim and not full:
        for key, body in entries.items():
            if "- Status: **PROVED**" not in body and "- Status: **EXPOSITORY**" not in body:
                if key.lower() not in readme:
                    raise ValueError(f"README must name remaining obligation: {key}")
    print(f"Ledger audit: {len(entries)} entries, acyclic dependencies; all {len(labels)} named results covered.")


if __name__ == "__main__":
    check_lean()
    check_ledger()
