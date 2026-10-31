# Checking evidence

The recorded verdict for the checked mathematical package is
[certificate.json](certificate.json): the exact combined M01/M02/M03
benchmark passed ordinary Linux sandboxed Comparator and all six configured
kernels, with actual exit 0 in 1464.250 seconds. This is a local checking
certificate produced before the public upload and Palomar submission.

The module documentation in `Challenge.lean` and `Solution.lean` has since
been corrected in response to Palomar's checking-status feedback. The old
unchecked-proposal wording described the initial draft, before the recorded
successful comparison. `documentation-status-update.json` records this
documentation-only correction. The exact checked source files, previous
package checker and previous version of this index are preserved under
`provenance/before-status-documentation-update/`. The certificate and raw
checking logs remain unchanged and refer to those predecessor bytes. No new
Lean or kernel run is claimed for the documentation correction.

## Actual runs

- `checks/diagnostics03/`: successful build (29.006 seconds), separately
  compiled Challenge/Solution statement inspections, full private proof
  inspection (402.707 seconds), and three actual axiom reports.
- `checks/comparator-final01/`: the final selected axiom audit, complete
  ordinary sandboxed `lake comparator --config comparator.json --paranoid`
  output, result, status and executable/dependency versions.
- `checks/dependencies-HEAD-and-platform.json`: actual local Git checks of
  all nine dependencies against their pinned HEAD, including staged and
  unstaged tracked changes; Python, bubblewrap and Linux versions.
- `checks/actual-remote-producer.json`: the actual as-run driver and fixed
  proof/interface/probe hashes.
- `checks/source-import-closure.txt` and `source-import-closure.json`: Lean's
  actual imported project-module table agrees with all 992 curated sources.
- `checks/metadata-preflight-03.txt`: actual final metadata/schema and
  package-structure validation. The earlier `01` and `02` preserve their cuts.

The initial cached-dependency copy materialized two tracked Mathlib script
symlinks, so the clean-tree preflight stopped before compilation. Their exact
internal relative links were restored without changing Lean source. A copied
Batteries README symlink caused the warnings retained in the diagnostic logs;
it was likewise restored. The exact repair receipts are identified in the
compiled review. All nine dependencies subsequently passed the separate
HEAD cleanliness check and the final gate's own dependency preflight.
The failed preparation cut remains in the preserved working development;
it is not a failed mathematical proof or a replacement checking verdict.

## Statement and proof inspection

`compiled-diagnostics.json` compares 104 actual statement dependencies:
25 definitions and 79 theorem helpers. The complete private project closure
has 5,684 dependencies plus the selected theorem. All inspected project
constants have safe, total kinds. The probes use actual originating modules,
including private declarations and imported namespaces; individual row
origins are not separately serialized. Expression hashes are auxiliary
diagnostics. The ordinary Comparator checks the actual exported constants;
the six kernels check the genuine proof.

Challenge contains 26 complete data declarations and three proved helpers.
The retained `fisherInformation` owner is complete and reviewed but lies
outside this selected statement's ordinary TYPE traversal. It is not
advertised as body-fixed through that traversal. The relative information
and Dirichlet definitions used by the selected results are reached.

The only deliberate placeholder is the selected theorem in Challenge.
Solution never imports Challenge; its actual axiom reports contain only
`propext`, `Classical.choice` and `Quot.sound`. There are no definition holes.

## Reviews, versions and historical cuts

`reviews/canonical_interface_static_B.*` and
`reviews/submission-interface-review.json` cover the new complete canonical
data, exact three-result type, genuine proof application and config.
`reviews/compiled-diagnostics-review.*` independently examine the actual raw
diagnostics. `reviews/package_documentation_review_C.*` and its README
addendum cover the exposition, correspondence, licences and provenance.
The final post-check integrity review has its separate
`reviews/final_package_review_E.json` receipt. All these reviews are AI
reviews, with source-authorship boundaries disclosed.

`reviews/prior/` preserves historical reviews, with original checking cuts
and development-relative references. They include supporting claims outside
the current selected conjunction. Their origin maps and source-review index
distinguish them from the new package verdict. The complete earlier working
development is preserved separately.

The exact diagnostic and final-gate driver sources are retained as `.txt`
documents under `provenance/`. The public replay runner adds a stronger
cached HEAD preflight and more precise reporting, with unchanged Lean
commands. `tooling-version-history.json` and complete diffs distinguish these
versions. No strengthened preflight is retroactively attributed to an earlier
run; the actual HEAD supplement supplies its own evidence.

`provenance/precheck-formalization.yaml` preserves the metadata reviewed
before the gate. `metadata-acceptance-delta.json` lists the factual status
updates after actual acceptance. Earlier pending flags describe those
historical cuts. Those records describe the accepted metadata cut before the later author-requested
publication metadata update. The current root metadata and certificate govern this package.

`documentary-corrections.json` preserves the first post-gate cut and resolves
two review findings: explicit authorship of the new combined interface and
the LF/CRLF distinction for the auxiliary import-header inspection source.
The actual invoked LF bytes and their own hash are retained separately from
the Windows documentary copy. No theorem, proof or checking verdict changed.

`publication-metadata-update.json` documents the authors' subsequent title and
joint-authorship request. The predecessor metadata, documentation, certificate
and payload manifest are preserved under
`provenance/before-publication-metadata-update/`. The earlier independent AI
package review applies to that predecessor; all Lean files, configuration,
toolchain pins and actual kernel-check outputs remain byte-identical. The new
metadata has its own schema check in `checks/metadata-preflight-04.txt`.

`payload-sha256.json` freezes every delivered file except itself after the
latest documentation-status correction. Run `python3 scripts/check_package.py`
from the repository root to check that payload and the recorded verdict.
The checker validates the certificate and raw log against the preserved
checked files, and requires every byte outside the single module comment in
each current Challenge/Solution file to match its checked predecessor.
It also checks the current documentation, checker and index hashes against
the correction record. This file check does not replace replaying Lean and
Comparator on the new submission commit.
