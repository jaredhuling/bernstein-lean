#!/usr/bin/env python3
"""Build and audit this checkout. No dependency updates or downloads are performed.

Requires Python 3.11+, elan, and the dependency cache described in README.md.
Generated drivers and evidence are written below .lake/verification by default.
"""
import argparse
import hashlib
import json
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
MODULES = ["Analytic", "MGF", "CGF", "General", "Bounded", "Product", "Statement",
           "Variance", "Frequency", "Examples", "BoundaryTests"]
HEADER = """/-
Copyright (c) 2026 Jared Huling. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Jared Huling
-/
module

"""


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def normalized_type(value):
    return " ".join(value.split())


def signature_hash(record):
    return hashlib.sha256(normalized_type(record.get("canonical_type", record["elaborated_type"])).encode()).hexdigest()


def declarations(source):
    """Index this project's explicit declarations; Lean supplies their actual types."""
    stack, names = [], []
    for line in source.splitlines():
        if re.match(r"^(?:(?:public|private|protected)\s+)*axiom\s", line):
            raise ValueError("Custom axiom declaration in library source")
        if re.match(r"^(?:(?:public|private|protected|unsafe|noncomputable)\s+)*"
                    r"(?:opaque|structure|class|inductive|instance)\b", line):
            raise ValueError("Unsupported declaration form; extend and review the audit index")
        if re.match(r"^(?:public|protected|unsafe|noncomputable)\s+"
                    r"(?:theorem|lemma|def|abbrev)\b", line):
            raise ValueError("Unsupported declaration modifier; extend and review the audit index")
        match = re.match(r"^(namespace|section)\s+(\S+)", line)
        if match:
            stack.append((match[1], match[2]))
        match = re.match(r"^end\s+(\S+)", line)
        if match:
            if not stack or stack[-1][1] != match[1]:
                raise ValueError(f"Unrecognized scope boundary: {line}")
            stack.pop()
        match = re.match(r"^(?:@\[[^\]]+\]\s*)?(?:private )?(?:theorem|lemma|def|abbrev)\s+(\w+)", line)
        if match:
            names.append(".".join([n for kind, n in stack if kind == "namespace"] + [match[1]]))
    if stack:
        raise ValueError(f"Unclosed named source scopes: {stack}")
    return names


def parse_records(log, expected):
    if re.search(r"error(?:\([^)]*\))?:", log) or "sorryAx" in log:
        raise ValueError("Lean errors or sorryAx in audit output")
    records = [json.loads(line.removeprefix("AUDIT_DECLARATION "))
               for line in log.splitlines() if line.startswith("AUDIT_DECLARATION ")]
    for record in records:
        required = {"declaration", "axioms", "binders", "elaborated_type", "canonical_type",
                    "conclusion", "direct_proof_dependencies"}
        if not isinstance(record, dict) or not required <= set(record):
            raise ValueError("Malformed audit record")
        if not isinstance(record["axioms"], list) or not all(
                isinstance(a, str) for a in record["axioms"]):
            raise ValueError("Malformed axiom inventory")
        if not isinstance(record["binders"], list):
            raise ValueError("Malformed binder inventory")
        for index, binder in enumerate(record["binders"]):
            if (binder.get("index") != index or
                    not isinstance(binder.get("is_proposition"), bool) or
                    not isinstance(binder.get("type"), str) or
                    not isinstance(binder.get("name"), str) or
                    binder.get("kind") not in {"explicit", "implicit", "strict-implicit", "instance"}):
                raise ValueError("Incomplete or reordered binder inventory")
    actual = [record["declaration"] for record in records]
    if len(actual) != len(set(actual)) or set(actual) != set(expected):
        raise ValueError("Missing, duplicate, or unexpected audit declarations")
    for record in records:
        if not set(record["axioms"]) <= ALLOWED_AXIOMS:
            raise ValueError(f"Unexpected axioms: {record['declaration']}")
    return records


def check_composition(records):
    by_name = {r["declaration"]: r for r in records}
    required = json.loads((ROOT / "verification/proof_edges.json").read_text())
    for caller, callees in required.items():
        actual = by_name[caller]["direct_proof_dependencies"]
        for callee in callees:
            # Private kernel names include a fresh generated-driver prefix.
            if not any(n == callee or (n.startswith("_private.") and
                                      n.endswith("." + callee)) for n in actual):
                raise ValueError(f"Reviewed proof edge missing: {caller} -> {callee}")


def check_review(records, review):
    expected = review["declarations"]
    if set(expected) != {r["declaration"] for r in records}:
        raise ValueError("Declaration set changed; review the new statement inventory")
    for record in records:
        entry = expected[record["declaration"]]
        if signature_hash(record) != entry["signature_sha256"]:
            raise ValueError(f"Statement changed: {record['declaration']}")
        indices = {b["index"] for b in record["binders"] if b["is_proposition"]}
        classified = {int(i) for i in entry["proposition_binders"]}
        if indices != classified:
            raise ValueError(f"Incomplete premise inventory: {record['declaration']}")
        allowed = {"reference-assumes", "reference-derives", "reference-cites", "lean-proves-applied", "formalization-specific"}
        if any(p.get("provenance") not in allowed or not p.get("evidence", "").strip()
               for p in entry["proposition_binders"].values()):
            raise ValueError(f"Unclassified premise or missing evidence: {record['declaration']}")
    for rel, expected_hash in review["definition_context_sha256"].items():
        if sha256(ROOT / rel) != expected_hash:
            raise ValueError(f"Reviewed definition/version context changed: {rel}")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", type=Path, default=ROOT / ".lake/verification")
    parser.add_argument("--skip-build", action="store_true",
                        help="Development only; CI and release checks must build")
    parser.add_argument("--inventory-only", action="store_true",
                        help="Emit evidence for manual review; never reports release success")
    args = parser.parse_args()
    out = args.out.resolve()
    out.mkdir(parents=True, exist_ok=True)
    # Never leave a success marker from an older run after a new failure.
    result_path = out / "result.json"
    result_path.write_text(json.dumps({"status": "running"}) + "\n")
    start = time.monotonic()
    checks = []

    def run(name, command):
        before = time.monotonic()
        with (out / f"{name}.log").open("w") as stream:
            result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        checks.append({"name": name, "command": command, "exit_code": result.returncode,
                       "seconds": round(time.monotonic() - before, 2)})
        (out / "commands.json").write_text(json.dumps(checks, indent=2) + "\n")
        log = (out / f"{name}.log").read_text()
        if result.returncode or "error:" in log or "sorryAx" in log or "warning:" in log:
            raise RuntimeError(f"{name} failed; see {out / (name + '.log')}")
        print(f"PASS {name}", flush=True)
        return log

    def lean(name, source):
        path = out / f"{name}.lean"
        path.write_text(source)
        return run(name, ["lake", "env", "lean", "-DwarningAsError=true", str(path)])

    dependencies = json.loads((ROOT / "lake-manifest.json").read_text())["packages"]
    dependency_revisions = {}
    for dependency in dependencies:
        if dependency.get("type") != "git":
            raise ValueError(f"Unpinned dependency: {dependency['name']}")
        folder = ROOT / ".lake/packages" / dependency["name"]
        rev = subprocess.check_output(["git", "-C", str(folder), "rev-parse", "HEAD"], text=True).strip()
        dirty = subprocess.check_output(
            ["git", "-C", str(folder), "status", "--porcelain", "--untracked-files=no"], text=True)
        if rev != dependency["rev"] or dirty:
            raise ValueError(f"Dependency differs from manifest: {dependency['name']}")
        dependency_revisions[dependency["name"]] = rev
    (out / "dependency_revisions.json").write_text(json.dumps(dependency_revisions, indent=2) + "\n")

    if not args.skip_build:
        run("build", ["lake", "build", "--wfail"])
        run("examples", ["lake", "test", "--wfail"])
    run("audit_tool_tests", [sys.executable, "scripts/test_verify.py"])
    run("original_statements", ["lake", "env", "lean", "-DwarningAsError=true",
                                "verification/OriginalStatements.lean"])
    source_modules = {str(p.relative_to(ROOT / "BernsteinLean")).removesuffix(".lean")
                      for p in (ROOT / "BernsteinLean").rglob("*.lean")}
    if source_modules != set(MODULES):
        raise ValueError("Library module set changed; extend and review the audit scope")
    names, sources, imports = [], [], {"Lean"}
    for module in MODULES:
        text = (ROOT / "BernsteinLean" / f"{module}.lean").read_text()
        names.extend(declarations(text))
        imports.update(re.findall(r"^(?:public )?import (Mathlib\.\S+)", text, re.M))
        text = re.sub(r"^(?:public )?import .*\n|^module\n", "", text, flags=re.M)
        sources.append(text)
    if len(names) != len(set(names)):
        raise ValueError("Duplicate source declaration names")
    audit_commands = (ROOT / "verification/AuditCommands.lean.inc").read_text()
    compiled = HEADER + "public import Lean\n"
    compiled += "\n".join("import all BernsteinLean." + m.replace("/", ".") for m in MODULES) + "\n\n"
    compiled += "/-! # Compiled declaration audit -/\n\n" + audit_commands
    compiled += "\n" + "\n".join("audit_decl " + n for n in names) + "\n"
    imported = parse_records(lean("compiled_audit", compiled), names)
    fresh = HEADER + "\n".join("public import " + n for n in sorted(imports)) + "\n\n"
    fresh += "/-! # Source proof-body audit -/\n\n"
    fresh += "\n\n".join(sources) + "\n\n" + audit_commands
    fresh += "\n" + "\n".join("audit_source_decl " + n for n in names) + "\n"
    records = parse_records(lean("source_audit", fresh), names)
    if {r["declaration"]: signature_hash(r) for r in records} != {
            r["declaration"]: signature_hash(r) for r in imported}:
        raise ValueError("Fresh and compiled declaration signatures differ")
    check_composition(records)
    (out / "declarations.json").write_text(json.dumps(records, indent=2, ensure_ascii=False) + "\n")
    roots = HEADER + """public import Lean
import BernsteinLean

/-! # Generic root import boundary -/

open Lean Elab Command
run_cmd do
  let modules := (← getEnv).header.moduleNames
  let forbidden := modules.filter fun n =>
    (`FoML).isPrefixOf n || (`StatLean).isPrefixOf n ||
    n == `BernsteinLean.Examples || n == `BernsteinLean.BoundaryTests ||
    n == `BernsteinLeanTest
  unless forbidden.isEmpty do throwError "Unexpected root imports: {forbidden}"
  logInfo m!"ROOT_MODULES {modules.size}; forbidden imports: {forbidden}"
"""
    lean("root_imports", roots)
    # Deliberately test that the actual Lean auditor rejects a custom axiom.
    negative = HEADER + "public import Lean\nimport BernsteinLean\n\n" + audit_commands
    negative += "\npublic axiom verificationRejectedAxiom : False\naudit_decl verificationRejectedAxiom\n"
    negative_path = out / "reject_axiom.lean"
    negative_path.write_text(negative)
    command = ["lake", "env", "lean", str(negative_path)]
    bad = subprocess.run(command, cwd=ROOT, text=True, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT)
    (out / "reject_axiom.log").write_text(bad.stdout)
    if bad.returncode == 0 or "Unexpected axioms for verificationRejectedAxiom" not in bad.stdout:
        raise ValueError("Axiom rejection check did not fail for the intended reason")
    print("PASS custom axiom rejected", flush=True)
    # Bind the evidence to the checked source, audit tooling, and dependency revisions.
    files = [p for p in ROOT.rglob("*") if p.is_file()
             and not any(part in {".lake", ".git", "__pycache__"} for part in p.relative_to(ROOT).parts)]
    hashes = {str(p.relative_to(ROOT)): sha256(p) for p in sorted(files)}
    (out / "source_hashes.json").write_text(json.dumps(hashes, indent=2) + "\n")
    if not args.inventory_only:
        review = json.loads((ROOT / "verification/reviewed_statements.json").read_text())
        check_review(records, review)
    result = {"status": ("inventory-only" if args.inventory_only else
                         "development-pass" if args.skip_build else "pass"),
              "build_performed": not args.skip_build,
              "declarations": len(records), "seconds": round(time.monotonic() - start, 2),
              "axioms_allowed": sorted(ALLOWED_AXIOMS), "root_imports": "generic only",
              "statement_regressions": "18 original public theorem types",
              "scope": "Standalone Bernstein library and its examples"}
    result_path.write_text(json.dumps(result, indent=2) + "\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    try:
        main()
    except Exception as error:
        print(f"VERIFICATION FAILED: {error}", file=sys.stderr)
        sys.exit(1)
