#!/usr/bin/env python3
"""Source-only preparation, the fixed FIVE checks, and fresh Lean kernel replay."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import tempfile
import time

ROOT = Path(__file__).resolve().parents[1]
SOURCE_MANIFEST = ROOT / "verification/sources.json"
PINS = ROOT / "verification/dependencies.json"
ALLOWED_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
SEARCH_TERMS = ["sorry", "admit", "unsafe", "partial", "native_decide", "axiom ",
                "constant ", "macro", "elab", "implemented_by", "extern"]


def fail(message):
    raise RuntimeError(message)


def manifest():
    return json.loads(SOURCE_MANIFEST.read_text(encoding="utf-8"))


def source_path(module):
    return ROOT / "src" / (module.replace(".", "/") + ".lean")


def clean_environment():
    env = os.environ.copy()
    for key in ("LEAN_PATH", "LEAN_SRC_PATH", "LEAN_SYSROOT", "LAKE_HOME", "LAKE_CACHE_DIR", "ELAN_TOOLCHAIN"):
        env.pop(key, None)
    env["MATHLIB_NO_CACHE_ON_UPDATE"] = "1"
    env["LAKE_NO_CACHE"] = "true"
    env["LAKE_ARTIFACT_CACHE"] = "false"
    env["LEAN_ABORT_ON_PANIC"] = "1"
    return env


def crash_dump_control():
    if os.name == "posix":
        import resource
        resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        if Path("/proc/self/coredump_filter").exists():
            Path("/proc/self/coredump_filter").write_text("0\n")


def new_capture(label):
    captures = ROOT / "verification/results"
    captures.mkdir(parents=True, exist_ok=True)
    folder = captures / (time.strftime("%Y%m%dT%H%M%S", time.gmtime()) + "-" + label + "-" + str(os.getpid()))
    folder.mkdir(exist_ok=False)
    return folder


def preflight(capture, label):
    # Check actual filesystems at this launch; there is no artificial reserve floor.
    paths = [ROOT, Path(tempfile.gettempdir()), Path.home()]
    if Path("/mnt/c").is_dir():
        # In WSL the physical host drive can differ from the Linux filesystem.
        paths.append(Path("/mnt/c"))
    lake_binary = shutil.which("lake")
    if lake_binary:
        paths.append(Path(lake_binary).resolve().parent)
    elan_home = os.environ.get("ELAN_HOME")
    if elan_home and Path(elan_home).exists():
        paths.append(Path(elan_home))
    rows = []
    for path in dict.fromkeys(p.resolve() for p in paths):
        disk = shutil.disk_usage(path)
        rows.append({"path": str(path), "total_bytes": disk.total,
                     "used_bytes": disk.used, "free_bytes": disk.free})
        if disk.free == 0:
            fail("No free disk space for launch on " + str(path))
    with (capture / "disk.jsonl").open("a", encoding="utf-8") as output:
        output.write(json.dumps({"label": label, "utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                                 "filesystems": rows}) + "\n")


def run(capture, label, command):
    preflight(capture, label)
    log = capture / (label + ".log")
    started = time.monotonic()
    print(label, flush=True)
    with log.open("w", encoding="utf-8", newline="\n") as output:
        result = subprocess.run(command, cwd=ROOT, env=clean_environment(),
                                stdout=output, stderr=subprocess.STDOUT)
    with (capture / "commands.jsonl").open("a", encoding="utf-8") as output:
        output.write(json.dumps({"label": label, "command": command, "exit_code": result.returncode,
                                 "elapsed_seconds": round(time.monotonic() - started, 3)}) + "\n")
    if result.returncode:
        print(log.read_text(encoding="utf-8", errors="replace"), file=sys.stderr)
        fail("Command failed; see " + str(log))
    return log


def static_check():
    data = manifest()
    rows = data["sources"]
    if len(rows) != data["source_count"] or data["source_count"] != 903:
        fail("Expected the complete 903-module reviewed project cone")
    modules = {r["module"] for r in rows}
    if len(modules) != 903:
        fail("Duplicate reviewed module")
    for row in rows:
        target = ROOT / row["path"]
        if target != source_path(row["module"]):
            fail("Unexpected module mapping: " + row["module"])
        if hashlib.sha256(target.read_bytes()).hexdigest() != row["sha256"]:
            fail("Source bytes differ from the reviewed snapshot: " + row["module"])
        for imported in row["imports"]:
            if imported not in modules and not imported.startswith(("Mathlib", "Lean", "Init", "Std", "Aesop", "Batteries", "Qq", "ProofWidgets", "Plausible", "ImportGraph", "LeanSearchClient", "Lake")):
                fail("Unpackaged project import: " + imported)
    pins = json.loads(PINS.read_text(encoding="utf-8"))
    lock = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    expected = {p["name"]: (p["url"], p["rev"]) for p in pins["packages"]}
    actual = {p["name"]: (p.get("url"), p.get("rev")) for p in lock["packages"] if p["type"] == "git"}
    if expected != actual or len(actual) != len(lock["packages"]):
        fail("Dependency lock differs from public revision pins")
    if (ROOT / "lean-toolchain").read_text().strip() != "leanprover/lean4:v4.33.1":
        fail("Incorrect Lean toolchain")
    print("Static checks passed: 903 byte-identical reviewed sources and 9 public Git pins.")


def prepare_dependencies():
    static_check()
    capture = new_capture("dependencies")
    for pin in json.loads(PINS.read_text())["packages"]:
        destination = ROOT / ".lake/packages" / pin["name"]
        destination.parent.mkdir(parents=True, exist_ok=True)
        if not destination.exists():
            run(capture, "clone-" + pin["name"], ["git", "clone", "--filter=blob:none", "--depth=1", "--no-checkout", pin["url"], str(destination)])
            run(capture, "fetch-" + pin["name"], ["git", "-C", str(destination), "fetch", "--depth=1", "origin", pin["rev"]])
            run(capture, "checkout-" + pin["name"], ["git", "-C", str(destination), "checkout", "--detach", pin["rev"]])
        head = run(capture, "head-" + pin["name"], ["git", "-C", str(destination), "rev-parse", "HEAD"]).read_text().strip()
        if head != pin["rev"]:
            fail("Dependency at wrong revision: " + pin["name"])
        status = run(capture, "status-" + pin["name"], ["git", "-C", str(destination), "status", "--porcelain", "--untracked-files=no"]).read_text().splitlines()
        permitted = [" M lean-toolchain"] if pin["name"] == "mathlib" else []
        if any(line not in permitted for line in status):
            fail("Unexpected tracked dependency changes: " + pin["name"])
        if pin["name"] == "mathlib":
            toolchain = destination / "lean-toolchain"
            old = toolchain.read_text().strip()
            if old not in ("leanprover/lean4:v4.33.0", "leanprover/lean4:v4.33.1"):
                fail("Unexpected pinned mathlib toolchain: " + old)
            toolchain.write_text("leanprover/lean4:v4.33.1\n", encoding="utf-8", newline="\n")
    print("Public dependencies are at the locked commits. Only mathlib's toolchain pin was adjusted to 4.33.1.")


def source_search(capture):
    hits = []
    for source in sorted((ROOT / "src").rglob("*.lean")):
        for line_number, line in enumerate(source.read_text(encoding="utf-8").splitlines(), 1):
            terms = [term for term in SEARCH_TERMS if term in line]
            if terms:
                hits.append(f"{source.relative_to(ROOT).as_posix()}:{line_number}: [{', '.join(terms)}] {line}")
    output = capture / "source-search.txt"
    output.write_text("\n".join(hits) + "\n", encoding="utf-8", newline="\n")
    print(f"FIVE 2: {len(hits)} plain-text hits; read source-search.txt and SOURCE_SEARCH_REVIEW.md.")


def source_order():
    rows = manifest()["sources"]
    dependencies = {r["module"]: r["imports"] for r in rows}
    dependencies.update({"Verification.Challenge": [],
                         "Verification.Binding": ["Verification.Challenge", "WPReview.AllPrime"],
                         "Verification.TypesAndAxioms": ["Verification.Binding"],
                         "WPSupercongruence": ["WPReview.AllPrime", "Verification.Binding"]})
    ordered, visiting, complete = [], set(), set()
    def visit(module):
        if module in complete:
            return
        if module in visiting:
            fail("Cyclic project imports at " + module)
        visiting.add(module)
        for imported in dependencies[module]:
            if imported in dependencies:
                visit(imported)
        visiting.remove(module)
        complete.add(module)
        ordered.append(module)
    for module in sorted(dependencies):
        visit(module)
    return ordered


def check_runtime(capture):
    log = run(capture, "lean-version", ["lake", "env", "lean", "--version"])
    version = log.read_text()
    if "version 4.33.1," not in version or "819816b2e0a3bf405af45ae5c7af2491d8f5bee6" not in version:
        fail("Expected the official audited Lean 4.33.1 runtime/commit")


def read_axioms(log):
    text = log.read_text(encoding="utf-8")
    matches = re.findall(r"depends on axioms:\s*\[([^\]]*)\]", text)
    # pp.universes prints these two permitted polymorphic axioms with .{u}.
    # Normalize only their observed spellings; keep the whitelist unchanged.
    printed_names = {"Classical.choice.{u}": "Classical.choice",
                     "Quot.sound.{u}": "Quot.sound"}
    sets = [{printed_names.get(item.strip(), item.strip())
             for item in match.split(",") if item.strip()} for match in matches]
    for axioms in sets:
        if not axioms <= ALLOWED_AXIOMS:
            fail("Unapproved axiom dependencies in " + str(log) + ": " + repr(axioms - ALLOWED_AXIOMS))
    named = (ROOT / "src/Verification/TypesAndAxioms.lean").read_text()
    expected = re.findall(r"^#print axioms (\S+)", named, re.MULTILINE)
    for theorem in expected:
        if "'" + theorem + "' depends on axioms:" not in text and "'" + theorem + "' does not depend on any axioms" not in text:
            fail("Missing explicit axiom output for " + theorem)
    print("FIVE 3: all named outputs have allowed axiom sets. Read the complete captured types and axioms.")
    print("FIVE 4: if a named report exposes another generated auxiliary, print that auxiliary's axioms and read them. No extra auxiliary is reported by the present transitive axiom output.")


def five():
    static_check()
    capture = new_capture("five")
    source_search(capture)
    check_runtime(capture)
    # Integration first builds all prerequisites in this source-only package.
    # Every project module uses the two strict compiler arguments in lakefile.toml.
    run(capture, "lake-build", ["lake", "build"])
    # The 903 reviewed proof providers are unchanged. The integration build
    # compiles them once with the strict arguments in lakefile.toml. The new
    # packaging unit consists of these four entry/verification sources.
    for module in ("Verification.Challenge", "Verification.Binding",
                   "Verification.TypesAndAxioms", "WPSupercongruence"):
        # Apply the explicit FIVE 1 command to each source of the new unit.
        # Its outputs are separate from the fresh Lake import providers.
        output = capture / "strict_objects" / (module.replace(".", "/") + ".olean")
        output.parent.mkdir(parents=True, exist_ok=True)
        log = run(capture, "strict-" + module, ["lake", "env", "lean", "--trust=0", "-DwarningAsError=true",
                    "--root=src", "-o", str(output), str(source_path(module))])
        if module == "Verification.TypesAndAxioms":
            read_axioms(log)
    print("FIVE commands completed. Human source-hit resolution and reading of the named types/axioms remain required.")
    print("Captures: " + str(capture))


def kernel():
    static_check()
    capture = new_capture("kernel")
    check_runtime(capture)
    run(capture, "fresh-kernel", ["lake", "env", "leanchecker", "--fresh", "--verbose", "Verification.Binding"])
    print("Fresh Lean kernel replay passed for the explicit literal challenge and complete imported proof cone.")
    print("Captures: " + str(capture))


def main():
    for stream in (sys.stdout, sys.stderr):
        if hasattr(stream, "reconfigure"):
            stream.reconfigure(encoding="utf-8", errors="replace")
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("stage", choices=("static", "dependencies", "five", "kernel"))
    args = parser.parse_args()
    crash_dump_control()
    {"static": static_check, "dependencies": prepare_dependencies, "five": five, "kernel": kernel}[args.stage]()


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError) as exc:
        print(str(exc), file=sys.stderr)
        sys.exit(1)
