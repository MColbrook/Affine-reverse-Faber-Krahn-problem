"""Read-only README wording delta/current-doc/provenance addendum; no Lean/network."""
from pathlib import Path
import hashlib
import json
import difflib

ROOT = Path(__file__).resolve().parents[2]
sha = lambda p: hashlib.sha256((ROOT/p).read_bytes()).hexdigest()
load = lambda p: json.loads((ROOT/p).read_text(encoding="utf-8"))
prior_path = "verification/reviews/package_documentation_review_C.json"
assert sha(prior_path) == "3befcda310d6b5c696c1dec0f73fc2397d51b1356728460b5e7b35b6a000a024"
prior = load(prior_path)
assert sha("verification/reviews/package_documentation_review_C.md") == "df03e01b2ec88ad1904bd46a3fdf9f97fd64e9ea2d3be0f3fe6db8df57e81cde"
assert sha("verification/reviews/package_documentation_review_C.py") == "215fd6f6cb73d8af0af46d972577d16a443464559a4dcf007f4dbce1c7bc5da6"
old_path = "verification/provenance/precheck-README.md"
old_meta = "verification/provenance/precheck-formalization.yaml"
assert sha(old_path) == prior["file_sha256"]["README.md"]
assert sha(old_meta) == prior["file_sha256"]["formalization.yaml"]
old = (ROOT/old_path).read_bytes()
new = (ROOT/"README.md").read_bytes()
before = (b"The first command may download dependencies; no dependency fetching occurs\n"
          b"in the Python checking runner. For timestamped, non-overwriting raw output:")
after = (b"The first command may download dependencies. The checking runner uses cached\n"
         b"dependencies and issues no explicit fetch command; Lake's own dependency\n"
         b"resolution remains network-capable. For timestamped, non-overwriting raw output:")
assert old.count(before) == 1 and old.replace(before, after) == new
docs = prior["documents_reviewed"]
for p in docs:
    if p != "README.md":
        assert sha(p) == prior["file_sha256"][p], p
provenance_path = "verification/provenance/upstream-source-map.json"
assert sha(provenance_path) == prior["file_sha256"][provenance_path]
source_pins_path = "verification/source-sha256.json"
assert sha(source_pins_path) == prior["file_sha256"][source_pins_path]
sources = load(source_pins_path)
assert len(sources) == 992
for p, pin in sources.items():
    assert sha(p) == pin, p
origin = load(provenance_path)
assert len(origin["rows"]) == 481
for group in origin["groups"].values():
    assert sha(group["license_path"]) == group["license_sha256"]
for row in origin["rows"]:
    data = (ROOT/row["original_copy"]).read_bytes()
    assert hashlib.sha256(data).hexdigest() == row["original_sha256"]
    assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest() == row["original_git_blob_sha1"]
    assert sha(row["proof_path"]) == row["proof_sha256"]
    assert sha(row["complete_source_diff"]) == row["diff_sha256"]
    text = lambda p: (ROOT/p).read_text(encoding="utf-8")
    actual_diff = "".join(difflib.unified_diff(text(row["original_copy"]).splitlines(keepends=True),
        text(row["proof_path"]).splitlines(keepends=True),
        fromfile=row["upstream_path"], tofile=row["proof_path"]))
    assert actual_diff == text(row["complete_source_diff"]), row["proof_path"]
unchanged_core = ["Challenge.lean", "Solution.lean", "AxiomAudit.lean", "comparator.json",
    "source/manuscript.tex", "AffineFK/MainTheorems.lean", "AffineFK/InformationSpectrumLogConcaveMeasure.lean"]
for p in unchanged_core:
    assert sha(p) == prior["file_sha256"][p], p
tooling_changes = []
for p in ["scripts/check_package.py", "scripts/run_checks.py"]:
    if sha(p) != prior["file_sha256"][p]:
        tooling_changes.append(dict(path=p, prior_existence_pin=prior["file_sha256"][p],
            current_sha256=sha(p), semantic_review_in_this_addendum=False,
            scope="Separate tooling-review ownership; not a mathematical, interface or documentation delta"))
paths = docs + [prior_path, "verification/reviews/package_documentation_review_C.md",
    "verification/reviews/package_documentation_review_C.py", old_path, old_meta,
    provenance_path, source_pins_path] + unchanged_core
report = dict(kind="Independent AI README dependency-fetch wording and current documentation addendum",
    reviewer="/root/claim_inventory", independent_AI_review_complete=True, findings=[],
    prior_review_immutable=True, exact_README_byte_delta_only=True,
    README_change="Replaces the overly absolute no-fetch assertion with no explicit runner fetch command and explicit network-capable child Lake dependency resolution.",
    semantic_assessment="The new wording is accurate for a runner using cached dependencies without an explicit fetch command; it does not promise network isolation of Lake's child dependency resolution. No mathematical scope, trust setting or theorem assumption changes.",
    current_documents=docs, seven_nonREADME_documents_byte_unchanged=True,
    historical_pin_resolutions={"README.md":dict(path=old_path, sha256=sha(old_path)),
        "formalization.yaml":dict(path=old_meta, sha256=sha(old_meta))},
    original_provenance_map_unchanged=True, proof_source_hashes_rechecked=992,
    original_snapshots_and_complete_differences_rechecked=481,
    separate_tooling_updates_not_reviewed_here=tooling_changes,
    actual_new_packet_acceptance_checked=False,
    certificate_pending_at_review_cut=not (ROOT/"verification/certificate.json").exists(),
    final_acceptance_evidence_required_separately=True,
    no_Lean_or_kernel_or_remote_or_GitHub_command=True,
    authorship_boundary="Independent of root-authored docs; reviewer authored the combined interface and some reused sources. This documentation-only addendum is not a second independent mathematical review of own proof bodies.",
    file_sha256={p:sha(p) for p in dict.fromkeys(paths)})
destination = Path(__file__).with_suffix(".json")
assert not destination.exists()
destination.write_text(json.dumps(report,indent=2)+"\n",encoding="utf-8")
print(json.dumps(dict(status="PASS", docs=8, exact_README_delta=True,
    source_hashes=992, origins_and_complete_diffs=481,
    report_sha256=hashlib.sha256(destination.read_bytes()).hexdigest(),
    compiler_or_kernel_run=False)))
