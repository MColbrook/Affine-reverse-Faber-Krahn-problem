"""Run real Lean tools and preserve output without explicit fetch commands.

Linux is required for the ordinary sandboxed Comparator. Provision the pinned
dependencies first. Lake's own resolver remains network-capable; this script
does not claim to provide an outer network-isolation boundary.
"""
from pathlib import Path
from concurrent.futures import ThreadPoolExecutor
import argparse
import hashlib
import json
import os
import platform
import shutil
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]
TARGET = "AffineFK.affine_reverse_faber_krahn_principal_results"

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def check_source():
    pins = json.loads((ROOT / "verification/source-sha256.json").read_text())
    assert len(pins) == 992
    for name, pin in pins.items():
        assert sha(ROOT / name) == pin, name

def record(command, destination):
    assert not destination.exists(), "Never overwrite a checking attempt"
    started = time.monotonic()
    with destination.open("x", encoding="utf-8") as stream:
        stream.write("COMMAND: " + json.dumps(command) + "\n")
        for tag, name in [("CONFIG", "comparator.json"), ("CHALLENGE", "Challenge.lean"),
                          ("SOLUTION", "Solution.lean"), ("SOURCES", "verification/source-sha256.json")]:
            stream.write(tag + "_SHA256: " + sha(ROOT / name) + "\n")
        stream.flush()
        result = subprocess.run(command, cwd=ROOT, stdout=stream, stderr=subprocess.STDOUT)
        stream.write("EXIT_CODE: " + str(result.returncode) + "\n")
        stream.write("ELAPSED_SECONDS: " + format(time.monotonic()-started, ".3f") + "\n")
    return result.returncode

def versions(lake):
    binary = Path(lake).resolve().parent
    tools = ["lean", "lake", "leanexport", "leanchecker", "leanchecker-paranoid",
             "lean4lean", "nanoda_bin", "con-leche", "con-ron"]
    suffix = ".exe" if os.name == "nt" else ""
    paths = {name: binary / (name + suffix) for name in tools}
    assert all(p.is_file() for p in paths.values()), paths
    baseline = json.loads((ROOT / "verification/provenance/accepted-toolchain.json").read_text())
    hashes = {name: sha(path) for name, path in paths.items()}
    assert hashes == baseline["binary_sha256"], "Use the pinned Linux x86_64 toolchain binaries"
    actual_versions = {name: subprocess.check_output([str(paths[name]), "--version"], text=True).strip()
                       for name in ["lean", "lake"]}
    assert actual_versions == baseline["versions"]
    dependencies = []
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    for package in manifest["packages"]:
        checkout = ROOT / manifest["packagesDir"] / package["name"]
        revision_command = ["git", "-C", str(checkout), "rev-parse", "HEAD"]
        cleanliness_command = ["git", "-C", str(checkout), "diff", "--quiet", "HEAD", "--"]
        revision = subprocess.check_output(revision_command, text=True).strip()
        assert revision == package["rev"], package["name"]
        subprocess.run(cleanliness_command, check=True)
        dependencies.append(dict(package=package["name"], pinned_commit=revision,
            tracked_clean=True, revision_command=revision_command,
            cleanliness_command=cleanliness_command))
    assert len(dependencies) == 9
    assert sha(ROOT / "lake-manifest.json") == baseline["lake_manifest_sha256"]
    return dict(versions=actual_versions, binary_sha256=hashes,
                mathlib_commit="b63f6e8a68d220e3b3bc4f3792bb53650d375f24",
                mathlib_clean=True, lake_manifest_sha256=sha(ROOT / "lake-manifest.json"),
                dependencies=dependencies, platform=platform.platform(),
                explicit_dependency_fetch_command_issued=False, outer_network_isolation_claimed=False)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("phase", choices=["diagnostics", "comparator"])
    parser.add_argument("--output", required=True, help="New relative output directory")
    parser.add_argument("--lake", default=shutil.which("lake"))
    args = parser.parse_args()
    assert platform.system() == "Linux", "Use Linux with real bwrap and user namespaces"
    assert args.lake
    lake = str(Path(args.lake).resolve())
    if not (Path(lake).parent / "leanexport").is_file():
        # Resolve the ordinary elan shim without assuming checker binaries live
        # beside the shim. The requested toolchain must already be installed.
        elan = shutil.which("elan")
        assert elan, "Pass --lake with the pinned toolchain's actual lake binary"
        lake = subprocess.check_output([elan, "which", "lake"], cwd=ROOT, text=True).strip()
        assert Path(lake).is_file()
    output = (ROOT / args.output).resolve()
    assert output.is_relative_to(ROOT) and output != ROOT
    output.mkdir(parents=True, exist_ok=False)
    check_source()
    config = json.loads((ROOT / "comparator.json").read_text())
    assert set(config) == {"challenge_module", "solution_module", "theorem_names", "definition_names", "permitted_axioms"}
    assert config["theorem_names"] == [TARGET] and config["definition_names"] == []
    assert config["challenge_module"] == "Challenge" and config["solution_module"] == "Solution"
    assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
    (output / "versions.json").write_text(json.dumps(versions(lake), indent=2)+"\n")
    status = output / "status.txt"
    if args.phase == "diagnostics":
        status.write_text("BUILD\n")
        code = record([lake, "build", "Challenge", "Solution", "AxiomAudit"], output / "build.txt")
        if code:
            status.write_text("BUILD_FAILED\n")
            raise SystemExit(code)
        status.write_text("COMPILED_DIAGNOSTICS\n")
        def probe(name):
            return record([lake, "env", "lean", "AuditTools/"+name+".lean"], output / (name+".txt"))
        with ThreadPoolExecutor(max_workers=3) as pool:
            codes = list(pool.map(probe, ["StatementChallenge", "StatementSolution", "ProofClosure"]))
        codes.append(record([lake, "env", "lean", "AxiomAudit.lean"], output / "axioms.txt"))
        status.write_text("COMPLETE\n" if all(c == 0 for c in codes) else "DIAGNOSTICS_FAILED\n")
        raise SystemExit(0 if all(c == 0 for c in codes) else 1)
    for name in ["submission-interface-review.json", "compiled-diagnostics-review.json"]:
        receipt = json.loads((ROOT / "verification/reviews" / name).read_text())
        assert receipt["independent_AI_review_complete"] is True
        for relative, pin in receipt["file_sha256"].items():
            assert sha(ROOT / relative) == pin, relative
    assert shutil.which("bwrap"), "A real ordinary sandbox is required"
    status.write_text("AXIOMS\n")
    ax = record([lake, "env", "lean", "AxiomAudit.lean"], output / "axioms.txt")
    if ax:
        status.write_text("AXIOMS_FAILED\n")
        raise SystemExit(ax)
    status.write_text("COMPARATOR\n")
    code = record([lake, "comparator", "--config", "comparator.json", "--paranoid"],
                  output / "comparator.txt")
    status.write_text("COMPLETE\n" if code == 0 else "COMPARATOR_FAILED\n")
    (output / "result.json").write_text(json.dumps(dict(actual_axioms_exit=ax,
        actual_comparator_exit=code, sandbox_disabled=False, status=status.read_text().strip(),
        selected_theorem=TARGET, full_manuscript_verified=False), indent=2)+"\n")
    raise SystemExit(code)

if __name__ == "__main__":
    main()
