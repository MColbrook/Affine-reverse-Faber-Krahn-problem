"""Portable read-only documentation/provenance review checks; no Lean/network.

The initial review is independent of the root-authored documentation, but its
author wrote the new combined interface and some reused proof foundations.
This does not substitute for their separate non-author mathematical reviews.
"""
from pathlib import Path
from collections import Counter
from urllib.parse import unquote, urlsplit
import difflib
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[2]
sha = lambda p: hashlib.sha256(p.read_bytes()).hexdigest()
read = lambda p: (ROOT / p).read_text(encoding="utf-8")
docs = ["README.md", "SUBMISSION.md", "CITATION.md", "NOTICE",
        "docs/correspondence.md", "docs/proof-departures.md", "docs/scope.md",
        "docs/third-party.md"]
assert all((ROOT/p).is_file() for p in docs)
assert "no substitute or invented identifier" not in read("SUBMISSION.md")
assert "This prepared package has\nnot been uploaded or registered." in read("SUBMISSION.md")
assert "(M01 ∧ M02) ∧ M03" in read("README.md")
assert "For every real `P ≥ 2`" in read("docs/correspondence.md")
assert "No smooth-boundary" in read("README.md")
assert "raw covariance" in read("docs/correspondence.md")
assert "Infinite information is never" in read("docs/correspondence.md")
assert "8 B + 4 n log 2" in read("docs/proof-departures.md")
assert "4 B + 2 n log 2" in read("docs/proof-departures.md")
assert "4^n/n!" in read("docs/proof-departures.md")
assert "strict positivity, simplicity" in read("docs/proof-departures.md")
assert "full unequal-input" in read("docs/scope.md")

# External reference URLs are identified, not fetched. The underlying primary
# reference audit is a retained historical document with its own provenance.
local_links, external_urls, missing = [], [], []
allowed_pending = {"verification/certificate.json"}
for name in docs:
    for label, dest in re.findall(r"\[([^\]]*)\]\(([^)]+)\)", read(name)):
        url = urlsplit(dest)
        if url.scheme:
            external_urls.append(dict(document=name, label=label, url=dest))
            continue
        rel = unquote(url.path)
        absolute = ((ROOT/name).parent/rel).resolve()
        assert absolute.is_relative_to(ROOT), (name, dest)
        portable = absolute.relative_to(ROOT).as_posix()
        row = dict(document=name, label=label, target=portable,
                   exists=absolute.exists())
        local_links.append(row)
        if not absolute.exists():
            missing.append(portable)
assert set(missing) <= allowed_pending, missing
# Important paths mentioned in prose/code spans, rather than Markdown links.
mentioned = ["scripts/check_package.py", "scripts/run_checks.py",
    "scripts/inspect_diagnostics.py", "AxiomAudit.lean", "comparator.json",
    "formalization.yaml", "source/manuscript.tex", "lake-manifest.json",
    "verification/formalization-v0.4.schema.json",
    "verification/provenance/upstream-source-map.json",
    "verification/reviews/prior/principal_manuscript_lean_correspondence_review.md",
    "verification/reviews/prior/principal_correspondence_calibration_review.md",
    "verification/reviews/prior/principal_proof_departure_review.md",
    "verification/reviews/prior/principal_background_reference_audit.md",
    "verification/reviews/prior/origin-map.json"]
assert all((ROOT/p).exists() for p in mentioned)
assert sha(ROOT/"source/manuscript.tex") == "1d30574bf6a09012c0492449d6860884c993b191837c9c0d2a9bd17080a3d0bc"
assert "Matthew J. Colbrook" in read("CITATION.md") and "George Stepaniants" in read("CITATION.md")
assert "does not\nrelicense source/manuscript.tex" in read("NOTICE")
assert "George Stepaniants is credited as a" in read("NOTICE")

sources = json.loads(read("verification/source-sha256.json"))
assert len(sources) == 992
for p, pin in sources.items():
    assert sha(ROOT/p) == pin, p
origin = json.loads(read("verification/provenance/upstream-source-map.json"))
assert len(origin["rows"]) == origin["selected_original_files"] == 481
counts = Counter(row["group"] for row in origin["rows"])
assert counts == {"OpenAI symmetric Mahler": 229, "Chafai MIT Brascamp-Lieb": 234,
    "Benenson Rellich": 15, "Ho Prekopa-Leindler source port": 2,
    "Armstrong-Loher Gaussian closure excerpt": 1}
assert len(sources)-sum(counts.values()) == 511
for group in origin["groups"].values():
    assert sha(ROOT/group["license_path"]) == group["license_sha256"]
mahler_exact = 0
for row in origin["rows"]:
    original_path = ROOT/row["original_copy"]
    proof_path = ROOT/row["proof_path"]
    data = original_path.read_bytes()
    assert len(data) == row["original_bytes"]
    assert hashlib.sha256(data).hexdigest() == row["original_sha256"]
    assert hashlib.sha1(b"blob "+str(len(data)).encode()+b"\0"+data).hexdigest() == row["original_git_blob_sha1"]
    assert sha(proof_path) == row["proof_sha256"] == sources[row["proof_path"]]
    assert sha(ROOT/row["complete_source_diff"]) == row["diff_sha256"]
    old = original_path.read_text(encoding="utf-8")
    new = proof_path.read_text(encoding="utf-8")
    actual_diff = "".join(difflib.unified_diff(old.splitlines(keepends=True),
        new.splitlines(keepends=True), fromfile=row["upstream_path"], tofile=row["proof_path"]))
    assert actual_diff == read(row["complete_source_diff"]), row["proof_path"]
    if row["group"] == "OpenAI symmetric Mahler":
        reversed_scaffold = re.sub(r"(?m)^module\n", "", new)
        reversed_scaffold = reversed_scaffold.replace("@[expose] public noncomputable section", "")
        reversed_scaffold = reversed_scaffold.replace("public import ", "import ").replace("AffineFK.OpenAIMahler", "OAI")
        nonblank = lambda s: "\n".join(line for line in s.splitlines() if line.strip())
        assert nonblank(old) == nonblank(reversed_scaffold), row["proof_path"]
        mahler_exact += 1
assert mahler_exact == 229
historical = json.loads(read("verification/reviews/prior/origin-map.json"))
for row in historical["files"].values():
    assert sha(ROOT/row["package_path"]) == row["sha256"]
config = json.loads(read("comparator.json"))
assert config["theorem_names"] == ["AffineFK.affine_reverse_faber_krahn_principal_results"]
assert config["definition_names"] == []
assert set(config["permitted_axioms"]) == {"propext", "Classical.choice", "Quot.sound"}
pin_names = docs + mentioned + ["Challenge.lean", "Solution.lean", "verification/source-sha256.json",
    "AffineFK/MainTheorems.lean", "AffineFK/InformationSpectrumLogConcaveMeasure.lean"]
report = dict(kind="Independent AI semantic documentation/attribution/local-link review",
    reviewer="/root/claim_inventory", independent_AI_review_complete=True, findings=[],
    documents_reviewed=docs, selected_claims=["M01", "M02", "M03"],
    theorem_domain_or_quantifier_correction_required=False,
    manuscript_modified=False, proofs_modified=False, build_or_kernel_run=False,
    network_or_GitHub_interaction=False, external_URLs_fetched=False,
    actual_new_package_acceptance_independently_checked_in_this_review=False,
    final_acceptance_evidence_required_separately=True,
    pending_finalization_paths=sorted(set(missing)),
    finalization_note="README/SUBMISSION describe the intended final accepted package. Do not publish its acceptance assertions unless the new exact combined packet certificate and raw actual gate evidence exist. Historical packet verdicts are not new-package acceptance.",
    local_Markdown_links=local_links, external_reference_URLs=external_urls,
    prose_or_command_paths_checked=mentioned, proof_source_hashes_checked=992,
    original_snapshot_hashes_and_Git_blob_ids_checked=481,
    complete_textual_differences_reconstructed=481, upstream_group_counts=dict(counts),
    license_hashes_checked=len(origin["groups"]),
    Mahler_files_identical_after_exact_import_visibility_scaffold_reversal=229,
    local_or_adapted_non_upstream_modules=511,
    resolved_style_observations=[
        "Owner replaced the invented-identifier defensive wording with direct URL/commit instructions.",
        "Owner replaced the verbose no-GitHub-contact sentence with the plain upload/registration status."],
    source_authorship_boundary="Reviewer did not author root README/SUBMISSION/CITATION/NOTICE/docs; reviewer authored the proposed combined interface, the retained correspondence audit and some reused probabilistic/Sobolev/geometric proofs. This review does not independently certify those own proof bodies or replace their separate non-author reviews. No human review or rereading all992 source proofs is claimed.",
    file_sha256={p:sha(ROOT/p) for p in dict.fromkeys(pin_names)})
destination = Path(__file__).with_suffix(".json")
assert not destination.exists(), "Preserve this completed documentary review; add a separate follow-up for later changes"
destination.write_text(json.dumps(report, indent=2)+"\n", encoding="utf-8")
print(json.dumps(dict(status="PASS", docs=len(docs), local_links=len(local_links),
    pending_finalization=sorted(set(missing)), source_hashes=992, origins_and_diffs=481,
    report_sha256=sha(destination), compiler_or_kernel_run=False)))
