"""Independent documentary parsing of completed diagnostics; never invokes Lean.

Run only after the AI reviewer has inspected the pinned probes and complete
canonical data. This records that review's actual evidence, not a proof oracle.
"""
from pathlib import Path
from collections import Counter
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
TARGET = "AffineFK.affine_reverse_faber_krahn_principal_results"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}
OWNER_MEANINGS = {
    "SobolevAmbient": "WithLp2 product of the actual scalar and vector L2 spaces",
    "testFunctionGradient": "Actual Frechet derivative followed by the inner-product dual identification",
    "gaussianPosition_matrix_det": "Genuine determinant identity for the matrix-induced Euclidean linear map",
    "gaussianPositionSLLinear": "Continuous linear equivalence induced by the literal real special-linear matrix",
    "GaussianPositionMaximal": "Actual standard Gaussian mass dominates every real special-linear image",
    "unweightedTestToL2": "Genuine L2 class of each compact smooth test",
    "unweightedSmoothPair": "Actual value-gradient test pair",
    "unweightedSobolevGraph": "Closure of actual compact smooth value-gradient pairs",
    "unweightedValue": "Continuous scalar L2 projection of the Sobolev graph",
    "unweightedGradient": "Continuous vector L2 projection of the Sobolev graph",
    "unweighted_smooth_pair_mem": "Genuine inclusion of a compact smooth pair in its graph closure",
    "dirichletTestToTop": "Zero-extension inclusion of compact smooth tests supported inside the open set",
    "dirichletTestToH1": "Actual value-gradient map of those supported tests into global H1",
    "dirichletSobolev": "Closure of supported compact tests in the actual global Sobolev graph",
    "dirichletValue": "Actual scalar L2 value map on the Dirichlet closure",
    "dirichletGradient": "Actual vector L2 weak-gradient map on the Dirichlet closure",
    "dirichletRayleigh": "Squared actual gradient norm divided by squared actual nonzero value norm",
    "dirichletEigenvalue": "Actual ENNReal infimum of Rayleigh quotients over nonzero Dirichlet values",
    "UniformSymmetricGaussianDirichletBound": "One C before all positive dimensions and symmetric volume-one maximal Gaussian bodies",
    "IsLogConcaveMeasure": "Conventional compact nonempty-set log-concavity inequality, including endpoint weights",
    "densityMeasure": "Actual Lebesgue measure with the nonnegative real density's ofReal weight",
    "sqrtDensitySobolev": "An actual Sobolev-graph vector representing sqrt(density) almost everywhere",
    "fisherInformation": "Ordinary square-root Sobolev information, with infinity outside that domain",
    "relativeFisherInformation": "Actual square-root Gaussian score energy with Sobolev and second-moment guards, infinity otherwise",
    "canonicalLebesgueDensity": "toReal of the actual Lebesgue Radon-Nikodym derivative",
    "relativeFisherMeasure": "Actual law-level relative information; infinity without absolute continuity",
    "poincare_euclidean_completeSpace": "Genuine named Mathlib PiLp completeness proof used explicitly in gradient data",
    "AdmissiblePoincareConstant": "Actual compact-smooth variance/gradient inequality with the named completeness proof",
    "poincareConstant": "Actual infimum of admissible nonnegative Poincare constants",
}
PROVED_OWNERS = {"gaussianPosition_matrix_det", "unweighted_smooth_pair_mem", "poincare_euclidean_completeSpace"}


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--logs", required=True, help="Completed relative diagnostics directory")
    args = parser.parse_args()
    directory = (ROOT / args.logs).resolve()
    assert directory.is_relative_to(ROOT)
    assert (directory / "status.txt").read_text(encoding="utf-8").strip() == "COMPLETE"
    pins = {}

    def pin(path):
        path = path.resolve()
        assert path.is_relative_to(ROOT)
        pins[path.relative_to(ROOT).as_posix()] = sha(path)

    def completed(name):
        path = directory / name
        raw = path.read_text(encoding="utf-8")
        assert re.findall(r"^EXIT_CODE: (-?\d+)$", raw, re.M) == ["0"], name
        assert "PANIC" not in raw and "panic!" not in raw, name
        commands = re.findall(r"^COMMAND: (.+)$", raw, re.M)
        assert len(commands) == 1, name
        command = json.loads(commands[0])
        expected = (["build", "Challenge", "Solution", "AxiomAudit"] if name == "build.txt" else
            ["env", "lean", "AxiomAudit.lean"] if name == "axioms.txt" else
            ["env", "lean", "AuditTools/" + name[:-4] + ".lean"])
        assert command[1:] == expected, (name, command)
        assert Path(command[0]).name == "lake", command
        for label, file in [("CHALLENGE", "Challenge.lean"), ("SOLUTION", "Solution.lean"),
                            ("CONFIG", "comparator.json"), ("SOURCES", "verification/source-sha256.json")]:
            assert re.findall(r"^" + label + r"_SHA256: ([a-f0-9]{64})$", raw, re.M) == [sha(ROOT / file)], (name, label)
        pin(path)
        return raw

    build = completed("build.txt")
    assert "Build completed successfully" in build

    def parse(name, marker, count_marker, ordinary=False):
        raw = completed(name)
        rows = [json.loads(line.split(marker + ": ", 1)[1]) for line in raw.splitlines()
                if line.startswith(marker + ": ")]
        counts = re.findall(r"^" + count_marker + r": (\d+)$", raw, re.M)
        assert len(counts) == 1 and len(rows) == int(counts[0]), name
        assert len({row["name"] for row in rows}) == len(rows), name
        for row in rows:
            assert row["kind"] in ({"definition", "theorem"} if ordinary else
                {"definition", "theorem", "opaque", "inductive", "constructor", "recursor"}), row
            assert row["is_unsafe"] is False and row["is_partial"] is False, row
            assert row["safety"].split(".")[-1] not in {"unsafe", "partial"}, row
            assert isinstance(row["project_constants"], list)
        headers = [json.loads(line.split("COMPILED_MAIN_JSON: ", 1)[1]) for line in raw.splitlines()
                   if line.startswith("COMPILED_MAIN_JSON: ")]
        assert len(headers) == 1 and headers[0]["name"] == TARGET
        assert headers[0]["level_params"] == []
        return raw, rows, headers[0]

    ch_raw, ch, ch_head = parse("StatementChallenge.txt", "COMPILED_CONSTANT_JSON", "COMPILED_ORDINARY_COUNT", True)
    sol_raw, sol, sol_head = parse("StatementSolution.txt", "COMPILED_CONSTANT_JSON", "COMPILED_ORDINARY_COUNT", True)
    full_raw, full, full_head = parse("ProofClosure.txt", "FULL_PROOF_CONSTANT_JSON", "FULL_PROOF_COUNT")
    assert ch == sol, "Complete independently parsed ordinary record sequences differ"
    assert ch_head == sol_head == full_head
    full_names = {row["name"] for row in full}
    assert TARGET not in full_names, "Selected root must be reported separately"
    assert {row["name"] for row in sol} <= full_names
    required = {"AffineFKProof.affine_reverse_faber_krahn_main_theorems",
                "AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant",
                "AffineFKProof.logConcaveMeasure_exists_density",
                "AffineFKProof.finite_relativeFisher_logConcaveMeasure_exists_density"}
    assert required <= full_names, required - full_names
    assert any(name.startswith("OAI.") for name in full_names), "Actual attributed Mahler proof constants missing"

    def axioms(raw):
        records = re.findall(r"'([^\n]+)' depends on axioms:\s*\[([^\]]*)\]", raw)
        output = []
        for name, body in records:
            used = {part.strip() for part in body.split(",") if part.strip()}
            assert used <= ALLOWED, (name, used)
            output.append({"declaration": name, "actual_axioms": sorted(used)})
        return output

    ax_raw = completed("axioms.txt")
    reports = axioms(ax_raw)
    assert len(reports) == 3
    assert {row["declaration"] for row in reports} == {
        "AffineFKProof.affine_reverse_faber_krahn_main_theorems",
        "AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant", TARGET}
    assert len(axioms(sol_raw)) == len(axioms(full_raw)) == 1
    main_axioms = next(row["actual_axioms"] for row in reports if row["declaration"] == TARGET)
    assert axioms(sol_raw)[0] == axioms(full_raw)[0] == {"declaration": TARGET, "actual_axioms": main_axioms}

    proof_probe = (ROOT / "AuditTools/ProofClosure.lean").read_text(encoding="utf-8")
    imports = re.findall(r"^import all (\S+)$", proof_probe, re.M)
    source_pins = json.loads((ROOT / "verification/source-sha256.json").read_text(encoding="utf-8"))
    assert len(source_pins) == 992
    modules = {name[:-5].replace("/", ".") for name in source_pins}
    assert set(imports) == modules | {"Solution"} and len(imports) == 993
    for file, expected in source_pins.items():
        assert sha(ROOT / file) == expected, file
    probe_names = ["AuditTools/StatementChallenge.lean", "AuditTools/StatementSolution.lean", "AuditTools/ProofClosure.lean"]
    for file in probe_names:
        source = (ROOT / file).read_text(encoding="utf-8")
        assert "env.getModuleIdxFor? n" in source
        assert 'm.startsWith "AffineFK." || m == "Solution" || m == "Challenge"' in source
        assert 'throwError "Unexpected ordinary project dependency kind' in source
        assert "if c.isUnsafe || c.isPartial then" in source
        assert 'getD' not in source and 'value!' not in source
    assert 'let mainProof ← match main with' in proof_probe
    assert '| .thmInfo v => pure v.value' in proof_probe
    assert 'main.type.getUsedConstants ++ mainProof.getUsedConstants' in proof_probe

    config = json.loads((ROOT / "comparator.json").read_text(encoding="utf-8"))
    assert config == {"challenge_module": "Challenge", "solution_module": "Solution", "theorem_names": [TARGET],
                      "definition_names": [], "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"]}
    type_names = {row["name"] for row in ch}
    owners = []
    for short, meaning in OWNER_MEANINGS.items():
        name = "AffineFK." + short
        owners.append({"name": name, "meaning_reviewed": meaning,
            "manual_kind": "genuine theorem helper" if short in PROVED_OWNERS else "data/abbreviation",
            "owner_itself_in_actual_ordinary_TYPE": name in type_names,
            "generated_or_subordinate_constants_in_TYPE": sorted(n for n in type_names if n.startswith(name + "."))})
    assert len(owners) == 29 and len(PROVED_OWNERS) == 3
    for file in probe_names + ["Challenge.lean", "Solution.lean", "AxiomAudit.lean", "comparator.json",
            "lean-toolchain", "lake-manifest.json", "verification/source-sha256.json",
            "verification/provenance/source-import-closure.json",
            "verification/provenance/interface-source-copy.json",
            "verification/reviews/canonical_interface_static_B.json"]:
        pin(ROOT / file)
    version_path = directory / "versions.json"
    actual_versions = json.loads(version_path.read_text(encoding="utf-8"))
    baseline = json.loads((ROOT / "verification/provenance/accepted-toolchain.json").read_text(encoding="utf-8"))
    assert actual_versions["binary_sha256"] == baseline["binary_sha256"]
    assert len(actual_versions["binary_sha256"]) == 9
    assert actual_versions["versions"] == baseline["versions"]
    assert actual_versions["mathlib_commit"] == "b63f6e8a68d220e3b3bc4f3792bb53650d375f24"
    assert actual_versions["mathlib_clean"] is True
    assert actual_versions["lake_manifest_sha256"] == sha(ROOT / "lake-manifest.json")
    cache_repair_path = ROOT / "verification/reviews/compiled-diagnostics-cache-repair-source.json"
    cache_repair = json.loads(cache_repair_path.read_text(encoding="utf-8"))
    manifest = json.loads((ROOT / "lake-manifest.json").read_text(encoding="utf-8"))
    manifest_pins = {row["name"]: row["rev"] for row in manifest["packages"]}
    assert {row["package"]: row["pinned_commit"] for row in cache_repair["packages"]} == manifest_pins
    assert all(row["tracked_clean"] is True for row in cache_repair["packages"])
    assert cache_repair["no_Lean_source_changes"] is True
    assert cache_repair["no_network_fetch"] is True
    assert [(row["package"], row["path"]) for row in cache_repair["restored_links"]] == [("batteries", "docs/README.md")]
    mathlib_repair_path = ROOT / "verification/reviews/compiled-diagnostics-Mathlib-link-repair-source.json"
    mathlib_repair = json.loads(mathlib_repair_path.read_text(encoding="utf-8"))
    assert mathlib_repair["actual_clean_check_exit"] == 0
    assert {row["path"] for row in mathlib_repair["rows"]} == {
        "scripts/bench/build/fake-root/bin/lean.py", "scripts/bench/size/run.py"}
    cache_warnings = sorted(set(re.findall(r"^warning: ([^:\n]+): repository has local changes:",
        build + ch_raw + sol_raw + full_raw + ax_raw, re.M)))
    assert cache_warnings == ["batteries"]
    pin(cache_repair_path)
    pin(mathlib_repair_path)
    pin(version_path)
    pin(ROOT / "verification/provenance/accepted-toolchain.json")
    pin(directory / "status.txt")
    pin(Path(__file__))
    out = ROOT / "verification/reviews/compiled-diagnostics-review.json"
    assert not out.exists(), "Preserve a completed independent review rather than overwrite it"
    result = {
        "kind": "Independent non-author AI actual compiled-diagnostics/tooling review; not a kernel oracle",
        "reviewer": "/root/palomar_requirements",
        "independent_AI_review_complete": True,
        "selected_theorem": TARGET,
        "scope": "Completed new-package build, independent raw ordinary TYPE/proof-closure parsing, axiom reports and probe integrity; previous source authorship is not represented as independent mathematical self-review",
        "all_diagnostic_fields_match": True,
        "actual_ordinary_TYPE_count": len(ch),
        "actual_ordinary_TYPE_kinds": dict(Counter(row["kind"] for row in ch)),
        "actual_proof_closure_excluding_selected_root": len(full),
        "actual_proof_closure_including_selected_root": len(full) + 1,
        "actual_full_closure_kinds": dict(Counter(row["kind"] for row in full)),
        "actual_namespace_counts_not_module_origin_counts": dict(Counter(row["name"].split(".")[0] for row in full)),
        "all_actual_isUnsafe_isPartial_flags_false": True,
        "actual_safety_suffixes_checked": True,
        "actual_main_header": ch_head,
        "complete_manual_owners": owners,
        "manual_data_owners_including_abbreviation": 26,
        "manual_genuine_helper_theorems": 3,
        "axiom_reports": reports,
        "actual_selected_axioms": main_axioms,
        "actual_versions_match_pinned_Linux_baseline": True,
        "actual_executable_hashes_matched": 9,
        "retained_diagnostic_cache_warnings": cache_warnings,
        "cache_warning_resolution": "Separate root-author source receipts, independently parsed here against all nine manifest pins, record exact tracked non-Lean internal symlink-form restoration; no Lean source edit. This reviewer did not rerun remote Git commands. Final gate must itself record all nine clean trees.",
        "full_private_imported_source_modules": 992,
        "all_private_imports_including_Solution": 993,
        "proof_classifier_uses_actual_origin_module": True,
        "per_row_origin_module_serialized": False,
        "origin_evidence_limit": "Actual getModuleIdxFor?-based classifier inspected in all three probes. Rows serialize names/kinds/flags/references, not origin_module. Namespace counts are not claimed as per-row module-origin tables.",
        "diagnostic_hash_limit": "Lean expression hash equality is diagnostic evidence; the required genuine Comparator checks exact exported ConstantInfo rather than treating these hashes as a proof oracle.",
        "new_package_comparator_acceptance_claimed": False,
        "required_next_check": "Own ordinary Linux sandboxed lake comparator --config comparator.json --paranoid, with all six actual acceptances",
        "github_interaction_or_rechecking_by_this_reviewer": False,
        "file_sha256": pins,
        "findings": [],
    }
    out.write_text(json.dumps(result, ensure_ascii=False, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"review": out.relative_to(ROOT).as_posix(), "sha256": sha(out),
        "ordinary_TYPE": len(ch), "full_including_root": len(full)+1, "axioms": main_axioms,
        "ordinary_owner_names_absent": [row["name"] for row in owners if not row["owner_itself_in_actual_ordinary_TYPE"]]}, indent=2))


if __name__ == "__main__":
    main()
