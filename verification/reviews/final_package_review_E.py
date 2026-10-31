"""Independent final file/evidence audit. Never invokes Lean, Git or a network.

The certificate hash must be supplied from the review handoff. This checks
recorded actual evidence; it does not replace replaying the genuine kernels.
"""
from pathlib import Path
from collections import Counter
import argparse
import ast
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
TARGET = "AffineFK.affine_reverse_faber_krahn_principal_results"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
LABELS = ["Lean paranoid kernel", "lean4lean kernel", "nanoda kernel",
          "con-leche kernel", "con-ron kernel", "Lean default kernel"]


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def load(path):
    return json.loads(path.read_text(encoding="utf-8"))


def changes(before, after, prefix=""):
    if isinstance(before, dict) and isinstance(after, dict):
        output = []
        for key in sorted(set(before) | set(after)):
            output.extend(changes(before.get(key), after.get(key), prefix + "/" + key))
        return output
    return [] if before == after else [{"path": prefix, "before": before, "after": after}]


def axiom_rows(text):
    output = {}
    for name, body in re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", text, re.M):
        assert name not in output
        used = {part.strip() for part in body.split(",") if part.strip()}
        assert used <= ALLOWED, (name, used)
        output[name] = sorted(used)
    return output


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--certificate-sha256", required=True)
    parser.add_argument("--metadata-sha256", required=True)
    args = parser.parse_args()
    pins = {}

    def pin(name):
        path = (ROOT / name).resolve()
        assert path.is_relative_to(ROOT) and path.is_file(), name
        pins[path.relative_to(ROOT).as_posix()] = sha(path)
        return path

    certificate_path = pin("verification/certificate.json")
    assert sha(certificate_path) == args.certificate_sha256
    certificate = load(certificate_path)
    frozen = certificate["file_sha256"]
    assert len(frozen) >= 2146
    assert "verification/reviews/final_package_review_E.json" not in frozen
    for name, expected in frozen.items():
        path = ROOT / name
        assert path.is_file() and not path.is_symlink(), name
        assert sha(path) == expected, name
    assert certificate["selected_theorem"] == TARGET
    assert certificate["original_manuscript_claims"] == ["M01", "M02", "M03"]
    assert certificate["actual_comparator_exit"] == 0 and certificate["sandbox_disabled"] is False
    assert certificate["kernel_acceptance_labels"] == LABELS
    assert certificate["full_manuscript_verified"] is False and certificate["human_review_claimed"] is False
    assert certificate["source_modules"] == 992 and certificate["compiled_Lean_files"] == 998
    assert certificate["private_proof_dependencies_including_root"] == 5685

    gate = ROOT / "verification/checks/comparator-final01"
    raw = pin(certificate["comparator_log"]).read_text(encoding="utf-8")
    commands = re.findall(r"^COMMAND: (.+)$", raw, re.M)
    assert len(commands) == 1
    assert json.loads(commands[0])[1:] == ["comparator", "--config", "comparator.json", "--paranoid"]
    assert re.findall(r"^EXIT_CODE: (-?\d+)$", raw, re.M) == ["0"]
    assert "Your solution is okay!" in raw and "PANIC" not in raw
    assert "Sandbox disabled" not in raw and "--inadvisably-no-sandbox" not in raw
    assert re.findall(r"^(.+ kernel) accepts the solution$", raw, re.M) == LABELS
    seconds = re.findall(r"^ELAPSED_SECONDS: ([0-9.]+)$", raw, re.M)
    assert len(seconds) == 1 and float(seconds[0]) == certificate["elapsed_seconds"] == 1464.25
    assert "checked 79192 declarations" in raw
    for checker in ["con-leche", "con-ron"]:
        assert checker + ": accepted 79191 declarations (--verified)" in raw
        assert checker + ": 1 inductive blocks modelled in-process: Lean.Syntax (30 generated records" in raw
    for tag, file in [("CONFIG", "comparator.json"), ("CHALLENGE", "Challenge.lean"),
                      ("SOLUTION", "Solution.lean"), ("SOURCES", "verification/source-sha256.json")]:
        assert re.findall(r"^" + tag + r"_SHA256: ([0-9a-f]{64})$", raw, re.M) == [sha(pin(file))]
    result = load(pin("verification/checks/comparator-final01/result.json"))
    assert result["actual_axioms_exit"] == result["actual_comparator_exit"] == 0
    assert result["status"] == "COMPLETE" and result["sandbox_disabled"] is False
    assert pin("verification/checks/comparator-final01/status.txt").read_text().strip() == "COMPLETE"
    ax_text = pin("verification/checks/comparator-final01/axioms.txt").read_text(encoding="utf-8")
    assert re.findall(r"^EXIT_CODE: (-?\d+)$", ax_text, re.M) == ["0"]
    ax = axiom_rows(ax_text)
    assert set(ax) == {TARGET, "AffineFKProof.affine_reverse_faber_krahn_main_theorems",
                       "AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant"}
    assert all(set(used) == ALLOWED for used in ax.values())
    assert {name: sorted(part.strip() for part in used.split(",") if part.strip())
            for name, used in certificate["actual_axiom_reports"].items()} == ax

    baseline = load(pin("verification/provenance/accepted-toolchain.json"))
    versions = load(pin("verification/checks/comparator-final01/versions.json"))
    assert versions["binary_sha256"] == baseline["binary_sha256"] and len(versions["binary_sha256"]) == 9
    assert versions["versions"] == baseline["versions"]
    manifest = load(pin("lake-manifest.json"))
    manifest_pins = {item["name"]: item["rev"] for item in manifest["packages"]}
    assert len(manifest_pins) == 9 and sha(ROOT / "lake-manifest.json") == versions["lake_manifest_sha256"]
    assert {item["package"]: item["pinned_commit"] for item in versions["dependencies"]} == manifest_pins
    assert all(item["tracked_clean"] is True for item in versions["dependencies"])
    supplement = load(pin("verification/checks/dependencies-HEAD-and-platform.json"))
    assert {item["package"]: item["pinned_commit"] for item in supplement["dependencies"]} == manifest_pins
    assert all(item["actual_cleanliness_exit"] == 0 and item["staged_and_unstaged_tracked_clean"] is True
               and item["cleanliness_command"][-4:] == ["diff", "--quiet", "HEAD", "--"]
               for item in supplement["dependencies"])
    assert all(item["exit_code"] == 0 for item in supplement["versions"])
    assert any(item["output"] == "bubblewrap 0.6.1" for item in supplement["versions"])

    producer = load(pin("verification/checks/actual-remote-producer.json"))
    for name, expected in producer["file_sha256"].items():
        actual_name = certificate["as_run_runner"] if name == "scripts/run_checks.py" else name
        assert sha(pin(actual_name)) == expected, name
    history = load(pin("verification/provenance/tooling-version-history.json"))
    for item in history["differences"]:
        before, after, difference = pin(item["before"]), pin(item["after"]), pin(item["diff"])
        assert sha(before) == item["before_sha256"] and sha(after) == item["after_sha256"]
        assert sha(difference) == item["diff_sha256"]
        expected = "".join(difflib.unified_diff(before.read_text(encoding="utf-8").splitlines(True),
            after.read_text(encoding="utf-8").splitlines(True), fromfile=item["before"], tofile=item["after"]))
        assert difference.read_text(encoding="utf-8") == expected, item["diff"]
    def function_asts(path):
        return {node.name: ast.dump(node, include_attributes=False) for node in
                ast.parse(path.read_text(encoding="utf-8")).body if isinstance(node, ast.FunctionDef)}
    as_run = function_asts(ROOT / certificate["as_run_runner"])
    public = function_asts(pin("scripts/run_checks.py"))
    assert set(as_run) == set(public)
    assert [name for name in as_run if as_run[name] != public[name]] == ["versions"]
    assert history["no_outer_airgap_claimed"] is True

    source_pins = load(pin("verification/source-sha256.json"))
    assert len(source_pins) == 992
    assert {path.relative_to(ROOT).as_posix() for path in (ROOT / "AffineFK").rglob("*.lean")} == set(source_pins)
    assert all(sha(ROOT / name) == expected for name, expected in source_pins.items())
    assert sum((ROOT / name).stat().st_size for name in source_pins) == 5508450
    module_names = {name[:-5].replace("/", ".") for name in source_pins}
    imported = load(pin("verification/source-import-closure.json"))
    import_raw = pin("verification/checks/source-import-closure.txt").read_text(encoding="utf-8")
    assert re.findall(r"^EXIT_CODE: (-?\d+)$", import_raw, re.M) == ["0"]
    actual_modules = re.findall(r"^PROJECT_IMPORTED_MODULE: (.+)$", import_raw, re.M)
    assert len(actual_modules) == len(set(actual_modules)) == 992
    assert set(actual_modules) == set(imported["project_modules"]) == module_names
    assert imported["all_actual_project_modules_packaged"] is True
    assert imported["extra_unbundled_project_modules"] == imported["missing_expected_modules"] == []
    assert imported["current_Solution_sha256"] == sha(ROOT / "Solution.lean")
    invoked = re.findall(r"^PROBE_SHA256: ([0-9a-f]{64})$", import_raw, re.M)
    assert len(invoked) == 1
    doc_probe = pin("verification/provenance/actual-import-closure-probe.lean.txt")
    assert hashlib.sha256(doc_probe.read_bytes().replace(b"\r\n", b"\n")).hexdigest() == invoked[0]
    def all_values(value):
        if isinstance(value, dict):
            return [leaf for item in value.values() for leaf in all_values(item)]
        if isinstance(value, list):
            return [leaf for item in value for leaf in all_values(item)]
        return [value]
    assert sha(doc_probe) in all_values(imported) and invoked[0] in all_values(imported)
    assert "LF" in json.dumps(imported), "Disclose invoked LF versus documentary CRLF bytes"
    invoked_copies = [path for path in (ROOT / "verification/provenance").glob("*import*probe*.txt") if sha(path) == invoked[0]]
    assert invoked_copies
    for path in invoked_copies:
        pin(path.relative_to(ROOT).as_posix())

    compiled = load(pin("verification/reviews/compiled-diagnostics-review.json"))
    assert compiled["independent_AI_review_complete"] is True
    assert compiled["actual_ordinary_TYPE_count"] == 104 and compiled["actual_proof_closure_including_selected_root"] == 5685
    for name, expected in compiled["file_sha256"].items():
        assert sha(ROOT / name) == expected, name
    for receipt in ["verification/reviews/submission-interface-review.json",
                    "verification/reviews/canonical_interface_static_B.json",
                    "verification/reviews/package_documentation_review_C.json"]:
        record = load(pin(receipt))
        assert record.get("independent_AI_review_complete", record.get("independent_static_review_complete")) is True
    static = load(ROOT / "verification/reviews/canonical_interface_static_B.json")
    assert static["complete_helper_declarations"] == 29 and static["complete_data_declarations_including_abbrev"] == 26

    provenance = load(pin("verification/provenance/upstream-source-map.json"))
    assert len(provenance["rows"]) == provenance["selected_original_files"] == 481
    for group in provenance["groups"].values():
        assert sha(ROOT / group["license_path"]) == group["license_sha256"]
    recomputed_differences = 0
    identical_text_pairs = 0
    for row in provenance["rows"]:
        original = ROOT / row["original_copy"]
        data = original.read_bytes()
        assert sha(original) == row["original_sha256"]
        assert hashlib.sha1(b"blob " + str(len(data)).encode() + b"\0" + data).hexdigest() == row["original_git_blob_sha1"]
        assert sha(ROOT / row["proof_path"]) == row["proof_sha256"]
        difference = ROOT / row["complete_source_diff"]
        assert sha(difference) == row["diff_sha256"]
        lines = difference.read_text(encoding="utf-8").splitlines(True)
        if lines:
            assert lines[0].startswith("--- ") and lines[1].startswith("+++ ")
            expected = "".join(difflib.unified_diff(original.read_text(encoding="utf-8").splitlines(True),
                (ROOT / row["proof_path"]).read_text(encoding="utf-8").splitlines(True),
                fromfile=lines[0][4:].rstrip("\n"), tofile=lines[1][4:].rstrip("\n")))
            assert "".join(lines) == expected, row["complete_source_diff"]
            recomputed_differences += 1
        else:
            assert original.read_text(encoding="utf-8") == (ROOT / row["proof_path"]).read_text(encoding="utf-8")
            identical_text_pairs += 1
    assert recomputed_differences + identical_text_pairs == 481

    metadata_path = pin("formalization.yaml")
    assert sha(metadata_path) == args.metadata_sha256 == certificate["metadata_sha256"]
    metadata = load(metadata_path)
    precheck = load(pin("verification/provenance/precheck-formalization.yaml"))
    delta = load(pin("verification/metadata-acceptance-delta.json"))
    assert delta["precheck_sha256"] == sha(ROOT / "verification/provenance/precheck-formalization.yaml")
    assert delta["accepted_sha256"] == sha(metadata_path)
    assert changes(precheck, metadata) == delta["differences"]
    for key in ["sources", "classification", "fidelity", "acknowledgements", "repository", "related_formalizations"]:
        assert metadata[key] == precheck[key], key
    for key in ["authors", "responsible_maintainers", "license", "name"]:
        assert metadata["project"][key] == precheck["project"][key]
    assert metadata["project"]["responsible_maintainers"] == ["Matthew J. Colbrook"]
    assert metadata["sources"][0]["authors"] == ["Matthew J. Colbrook", "George Stepaniants"]
    assert metadata["status"]["sorry_count"] == metadata["status"]["sorry_in_definitions"] == 0
    assert set(metadata["status"]["axioms"]) == ALLOWED
    assert metadata["verification"]["new_combined_package_acceptance_claimed"] is True
    assert metadata["verification"]["challenge_placeholder_count"] == 1
    assert metadata["verification"]["solution_and_proof_closure_placeholder_count"] == 0
    assert metadata["verification"]["definition_holes"] == []
    assert metadata["verification"]["full_manuscript_verified"] is False
    assert any("claim_inventory" in role and "author of this new combined canonical interface" in role
               for role in metadata["review"]["reviewers"])
    assert any("formalization_coverage" in role and "independent non-author reviewer of this new C-authored combined canonical interface" in role
               for role in metadata["review"]["reviewers"])
    corrections = load(pin("verification/documentary-corrections.json"))
    for prior in corrections["preserved_predecessors"].values():
        assert sha(pin(prior["preserved_path"])) == prior["sha256"]
    earlier_meta = load(ROOT / corrections["preserved_predecessors"]["formalization.yaml"]["preserved_path"])
    assert {item["path"] for item in changes(earlier_meta, metadata)} == {"/review/notes", "/review/reviewers"}
    assert corrections["current_metadata_sha256"] == sha(metadata_path)
    assert corrections["current_import_closure_report_sha256"] == sha(ROOT / "verification/source-import-closure.json")
    assert corrections["no_Lean_or_kernel_command_rerun"] is True
    schema = pin("verification/formalization-v0.4.schema.json")
    assert sha(schema) == certificate["schema_sha256"] == "25ff6b25ca4511635aff4443cf20480c15e59dddf19591c730950b442ea54fce"
    schema_logs = sorted((ROOT / "verification/checks").glob("metadata-preflight-*.txt"))
    current_schema = [path for path in schema_logs if "METADATA_SHA256: " + sha(metadata_path) in path.read_text(encoding="utf-8")]
    assert current_schema
    for path in current_schema:
        text = path.read_text(encoding="utf-8")
        assert re.findall(r"^EXIT_CODE: (-?\d+)$", text, re.M) == ["0"]
        assert '"schema_checked": true' in text and '"status": "PASS"' in text
        pin(path.relative_to(ROOT).as_posix())

    for pattern in ["docs/*.md", "scripts/*.py", "verification/reviews/package_documentation_readme_addendum_C.*"]:
        for path in ROOT.glob(pattern):
            if path.is_file():
                pin(path.relative_to(ROOT).as_posix())
    for name in ["README.md", "SUBMISSION.md", "CITATION.md", "NOTICE", "LICENSE", "verification/README.md",
                 "Challenge.lean", "Solution.lean", "AxiomAudit.lean", "comparator.json", "lakefile.toml", "lean-toolchain",
                 "AuditTools/StatementChallenge.lean", "AuditTools/StatementSolution.lean", "AuditTools/ProofClosure.lean",
                 "verification/compiled-diagnostics.json", "verification/reviews/compiled-diagnostics-review.md"]:
        pin(name)
    pin(Path(__file__).relative_to(ROOT).as_posix())
    md_path = ROOT / "verification/reviews/final_package_review_E.md"
    assert md_path.is_file(), "The AI review narrative must be completed before issuing the final receipt"
    pin(md_path.relative_to(ROOT).as_posix())
    # Recheck the author's frozen inputs after the documentary inspection.
    assert all(sha(ROOT / name) == expected for name, expected in frozen.items())
    output = ROOT / "verification/reviews/final_package_review_E.json"
    assert not output.exists(), "Do not overwrite a completed independent review"
    record = {
        "kind": "Independent AI final post-gate package integrity, evidence and disclosure review; not a kernel rerun",
        "reviewer": "/root/palomar_requirements",
        "independent_AI_review_complete": True,
        "selected_theorem": TARGET,
        "selected_original_claims": ["M01", "M02", "M03"],
        "all_frozen_certificate_input_hashes_match": True,
        "frozen_certificate_input_files_checked": len(frozen),
        "actual_six_kernel_acceptances_independently_read": LABELS,
        "actual_comparator_exit": 0,
        "actual_comparator_elapsed_seconds": 1464.25,
        "actual_Solution_axiom_reports": ax,
        "sandbox_disabled": False,
        "pinned_executable_hashes_checked_from_actual_records": 9,
        "pinned_dependency_HEAD_and_staged_unstaged_supplement_records_checked": 9,
        "unchanged_proof_source_modules": 992,
        "actual_Lean_imported_project_modules_match_packaged_sources": 992,
        "ordinary_TYPE_constants": 104,
        "ordinary_TYPE_definitions": 25,
        "ordinary_TYPE_theorem_helpers": 79,
        "actual_private_project_constants_including_root": 5685,
        "all_29_manual_owner_and_Fisher_generated_helper_scope_recorded": True,
        "original_Git_blobs_SHA256_and_ported_proof_hashes_checked": 481,
        "complete_textual_diffs_recomputed": recomputed_differences,
        "empty_diffs_verified_as_identical_normalized_text_pairs": identical_text_pairs,
        "current_metadata_is_only_factual_status_role_clarification_of_precheck": True,
        "source_IDs_authors_licences_math_scope_unchanged": True,
        "as_run_vs_public_runner_versions_explicit_and_checked": True,
        "header_probe_actual_LF_vs_documentary_CRLF_explicit_and_checked": True,
        "saved_schema_validation_actual_exit": 0,
        "saved_protocol_date": "2026-10-27",
        "current_online_policy_check_or_GitHub_interaction_by_reviewer": False,
        "Lean_Git_or_kernel_commands_executed_by_reviewer": False,
        "full_manuscript_verified": False,
        "human_review_claimed": False,
        "certificate_does_not_pin_this_future_review_no_hash_cycle": True,
        "payload_freeze_and_archive_creation_remain_parent_final_steps": True,
        "authorship_boundary": "Independent final evidence/tooling review; the reviewer authored several reused proof sources and does not claim a new independent mathematical review of those same proofs. Prior non-author source reviews and the B-authored review of C's new interface remain separate.",
        "file_sha256": pins,
        "findings": [],
    }
    output.write_text(json.dumps(record, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": "PASS", "review_sha256": sha(output), "frozen_files": len(frozen),
                      "proof_sources": 992, "provenance_originals": 481, "diffs_recomputed": recomputed_differences}, indent=2))


if __name__ == "__main__":
    main()
