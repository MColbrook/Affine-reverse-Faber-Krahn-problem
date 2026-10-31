"""Local file-integrity and saved-policy preflight. Does not invoke Lean or fetch.

Use --preflight while assembling the package; the default also requires the
final accepted certificate and the complete payload manifest. --schema adds
validation against the saved official schema using installed jsonschema.
"""
from pathlib import Path
import argparse
import hashlib
import json
import re
from lean_source import strip_comments

ROOT = Path(__file__).resolve().parents[1]
TARGET = "AffineFK.affine_reverse_faber_krahn_principal_results"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
IGNORED = {".lake", ".git", ".verification", ".venv", "__pycache__"}
STATUS_UPDATE_SNAPSHOTS = {
    name: "verification/provenance/before-status-documentation-update/" + Path(name).name + ".txt"
    for name in ("Challenge.lean", "Solution.lean", "scripts/check_package.py", "verification/README.md")
}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def payload():
    return sorted(p for p in ROOT.rglob("*") if p.is_file() and
        not any(part in IGNORED for part in p.relative_to(ROOT).parts))

def checked_snapshot(name):
    """The unchanged certificate and raw log identify these predecessor bytes."""
    return ROOT / STATUS_UPDATE_SNAPSHOTS.get(name, name)

def outside_module_documentation(data):
    """Remove only the single, non-nested module comment; retain all other bytes."""
    assert data.count(b"/-!") == 1, "Expected exactly one module comment"
    prefix, _, rest = data.partition(b"/-!")
    comment, close, suffix = rest.partition(b"-/")
    assert close and b"/-" not in comment, "Expected a closed, non-nested module comment"
    return prefix, suffix

def check_documentation_update():
    record = json.loads((ROOT / "verification/documentation-status-update.json").read_text())
    assert set(record["preserved_predecessors"]) == set(STATUS_UPDATE_SNAPSHOTS)
    assert set(record["current_file_sha256"]) == set(STATUS_UPDATE_SNAPSHOTS)
    for name, saved in STATUS_UPDATE_SNAPSHOTS.items():
        predecessor = record["preserved_predecessors"][name]
        assert predecessor["preserved_path"] == saved
        assert sha(ROOT / saved) == predecessor["sha256"], saved
        assert sha(ROOT / name) == record["current_file_sha256"][name], name
    for name in ("Challenge.lean", "Solution.lean"):
        assert outside_module_documentation((ROOT / name).read_bytes()) == \
            outside_module_documentation(checked_snapshot(name).read_bytes()), \
            f"Non-documentation bytes changed in {name}; a new verification run is required"

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--preflight", action="store_true")
    parser.add_argument("--schema", action="store_true")
    args = parser.parse_args()
    check_documentation_update()
    pins = json.loads((ROOT / "verification/source-sha256.json").read_text())
    assert len(pins) == 992
    actual = {p.relative_to(ROOT).as_posix() for p in (ROOT / "AffineFK").rglob("*.lean")}
    assert actual == set(pins)
    for name, pin in pins.items():
        assert sha(ROOT / name) == pin, name
    config = json.loads((ROOT / "comparator.json").read_text())
    assert config == dict(challenge_module="Challenge", solution_module="Solution",
        theorem_names=[TARGET], definition_names=[], permitted_axioms=["propext", "Classical.choice", "Quot.sound"])
    challenge = ROOT / "Challenge.lean"
    assert len(challenge.read_bytes().splitlines()) <= 1000
    assert len(challenge.read_bytes()) <= 100*1024
    clean_challenge = strip_comments(challenge.read_text(encoding="utf-8"))
    assert len(re.findall(r"\bsorry\b", clean_challenge)) == 1
    imports = re.findall(r"(?m)^(?:public\s+)?import\s+(?:all\s+)?(\S+)", clean_challenge)
    assert imports and all(name.startswith("Mathlib.") for name in imports)
    proof_files = [ROOT / "Solution.lean"] + [ROOT / name for name in pins]
    for path in proof_files:
        code = strip_comments(path.read_text(encoding="utf-8"))
        assert not re.search(r"\b(sorry|admit|axiom|native_decide|ofReduceBool|implemented_by|unsafe)\b", code), str(path)
        assert not re.search(r"(?m)^(?:public\s+)?import\s+(?:all\s+)?Challenge\b", code)
    files = payload()
    lean_files = [p for p in files if p.suffix == ".lean"]
    assert len(lean_files) == 998
    for path in lean_files:
        assert len(path.read_bytes().splitlines()) <= 10000, str(path)
        assert strip_comments(path.read_text(encoding="utf-8")).lstrip().startswith("module"), str(path)
    assert all(not path.is_symlink() for path in files)
    assert not [p for p in files if p.suffix.lower() in {".olean", ".ilean", ".o", ".obj", ".exe", ".dll", ".so", ".pyc"}]
    assert (ROOT / "lean-toolchain").read_text().strip() == "leanprover/lean4:v4.35.0-rc3"
    manifest = json.loads((ROOT / "lake-manifest.json").read_text())
    assert all(re.fullmatch(r"[0-9a-f]{40}", p["rev"]) for p in manifest["packages"])
    metadata = json.loads((ROOT / "formalization.yaml").read_text(encoding="utf-8"))
    assert metadata["status"]["sorry_count"] == metadata["status"]["sorry_in_definitions"] == 0
    assert set(metadata["status"]["axioms"]) == ALLOWED
    assert metadata["verification"]["challenge_placeholder_count"] == 1
    assert metadata["verification"]["solution_and_proof_closure_placeholder_count"] == 0
    if args.schema:
        import jsonschema
        schema = json.loads((ROOT / "verification/formalization-v0.4.schema.json").read_text())
        assert sha(ROOT / "verification/formalization-v0.4.schema.json") == "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"
        jsonschema.validate(metadata, schema)
    originals = json.loads((ROOT / "verification/provenance/upstream-source-map.json").read_text())
    assert len(originals["rows"]) == 481
    for group in originals["groups"].values():
        assert sha(ROOT / group["license_path"]) == group["license_sha256"]
    for row in originals["rows"]:
        path = ROOT / row["original_copy"]
        data = path.read_bytes()
        assert sha(path) == row["original_sha256"]
        assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest() == row["original_git_blob_sha1"]
        assert sha(ROOT / row["proof_path"]) == row["proof_sha256"]
        assert sha(ROOT / row["complete_source_diff"]) == row["diff_sha256"]
    if not args.preflight:
        certificate = json.loads((ROOT / "verification/certificate.json").read_text())
        assert certificate["actual_comparator_exit"] == 0
        assert certificate["sandbox_disabled"] is False
        expected_labels = {"Lean paranoid kernel", "lean4lean kernel", "nanoda kernel",
                           "con-leche kernel", "con-ron kernel", "Lean default kernel"}
        labels = certificate["kernel_acceptance_labels"]
        assert len(labels) == 6 and set(labels) == expected_labels
        assert certificate["selected_theorem"] == TARGET
        raw = (ROOT / certificate["comparator_log"]).read_text(encoding="utf-8")
        assert re.findall(r"^EXIT_CODE: (\d+)$", raw, re.M) == ["0"]
        assert "Your solution is okay!" in raw and "PANIC" not in raw
        assert "--inadvisably-no-sandbox" not in raw and "Sandbox disabled" not in raw
        raw_labels = re.findall(r"^(.+ kernel) accepts the solution$", raw, re.M)
        assert raw_labels == labels
        for tag, name in [("CONFIG", "comparator.json"), ("CHALLENGE", "Challenge.lean"),
                          ("SOLUTION", "Solution.lean"), ("SOURCES", "verification/source-sha256.json")]:
            assert tag+"_SHA256: "+sha(checked_snapshot(name)) in raw
        for name, pin in certificate["file_sha256"].items():
            assert sha(checked_snapshot(name)) == pin, name
        assert metadata["verification"]["new_combined_package_acceptance_claimed"] is True
        recorded = json.loads((ROOT / "verification/payload-sha256.json").read_text())
        current = {p.relative_to(ROOT).as_posix():sha(p) for p in files
                   if p.relative_to(ROOT).as_posix() != "verification/payload-sha256.json"}
        assert current == recorded, "Package payload changed after the final freeze"
    print(json.dumps(dict(status="PASS", proof_source_files=992, compiled_Lean_files=len(lean_files),
        source_bytes=sum((ROOT/p).stat().st_size for p in pins), Challenge_physical_lines=len(challenge.read_bytes().splitlines()),
        Challenge_bytes=challenge.stat().st_size, selected_originals=481,
        schema_checked=args.schema, preflight_only=args.preflight,
        documentation_only_update_checked=True, Lean_or_kernel_commands_run=False)))

if __name__ == "__main__":
    main()
