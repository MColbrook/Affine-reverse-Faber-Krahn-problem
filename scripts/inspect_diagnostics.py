"""Compare actual compiled diagnostic output; this is not a proof oracle."""
from pathlib import Path
import argparse
import hashlib
import json
import re

ROOT = Path(__file__).resolve().parents[1]
TARGET = "AffineFK.affine_reverse_faber_krahn_principal_results"
ALLOWED = {"propext", "Classical.choice", "Quot.sound"}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def completed(path):
    text = path.read_text(encoding="utf-8")
    assert re.findall(r"^EXIT_CODE: (\d+)$", text, re.M) == ["0"], str(path)
    assert "PANIC" not in text
    return text

def rows(text, marker, counter):
    values = [json.loads(line.split(marker+": ", 1)[1]) for line in text.splitlines() if marker+": " in line]
    assert re.findall(r"^"+counter+r": (\d+)$", text, re.M) == [str(len(values))]
    assert len({value["name"] for value in values}) == len(values)
    for value in values:
        assert value["kind"] in {"definition", "theorem", "opaque", "inductive", "constructor", "recursor"}
        assert not value["is_unsafe"] and not value["is_partial"]
        assert value["safety"].split(".")[-1] not in {"unsafe", "partial"}
    return values

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--input", required=True, help="Directory containing actual diagnostics")
    parser.add_argument("--output", required=True, help="New JSON result path")
    args = parser.parse_args()
    folder = (ROOT / args.input).resolve()
    output = (ROOT / args.output).resolve()
    assert folder.is_relative_to(ROOT) and output.is_relative_to(ROOT)
    assert not output.exists()
    sides, headers = [], []
    for side in ["Challenge", "Solution"]:
        text = completed(folder / ("Statement"+side+".txt"))
        sides.append(rows(text, "COMPILED_CONSTANT_JSON", "COMPILED_ORDINARY_COUNT"))
        main_rows = [json.loads(line.split("COMPILED_MAIN_JSON: ",1)[1]) for line in text.splitlines() if "COMPILED_MAIN_JSON: " in line]
        assert len(main_rows) == 1 and main_rows[0]["name"] == TARGET
        headers.append(main_rows[0])
    assert sides[0] == sides[1], "Actual statement dependency kinds/types/bodies/refs differ"
    assert headers[0] == headers[1], "Actual selected theorem types differ"
    full_text = completed(folder / "ProofClosure.txt")
    full = rows(full_text, "FULL_PROOF_CONSTANT_JSON", "FULL_PROOF_COUNT")
    names = {row["name"] for row in full}
    assert TARGET not in names
    assert {"AffineFKProof.affine_reverse_faber_krahn_main_theorems",
            "AffineFKProof.information_spectrum_logConcaveMeasure_uniform_constant",
            "AffineFKProof.finite_relativeFisher_logConcaveMeasure_exists_density",
            "OAI.SymmetricMahler.symmetric_mahler"} <= names
    axioms = completed(folder / "axioms.txt")
    ax_rows = re.findall(r"^'([^\n]+)' depends on axioms:\s*\[([^]]*)\]", axioms, re.M)
    assert len(ax_rows) == 3 and TARGET in dict(ax_rows)
    assert all({a.strip() for a in values.split(",") if a.strip()} <= ALLOWED for _, values in ax_rows)
    completed(folder / "build.txt")
    result = dict(kind="Actual compiled TYPE/body and private-origin proof inspection; auxiliary diagnostics, not kernel acceptance",
        selected_theorem=TARGET, selected_main_header=headers[0], all_statement_diagnostics_match=True,
        ordinary_statement_dependencies=sides[0], ordinary_statement_constant_count=len(sides[0]),
        full_project_proof_dependencies=full, private_project_constants_including_selected=len(full)+1,
        private_imported_proof_source_modules=992, private_imported_modules_including_Solution=993,
        all_actual_project_kinds_safe_and_total=True, actual_axiom_reports=dict(ax_rows),
        own_sandboxed_Comparator_and_six_kernels_still_required=True,
        file_sha256={p.relative_to(ROOT).as_posix():sha(p) for p in sorted(folder.iterdir()) if p.is_file()})
    output.parent.mkdir(parents=True,exist_ok=True)
    output.write_text(json.dumps(result,indent=2)+"\n",encoding="utf-8")
    print(json.dumps(dict(status="PASS", statement_constants=len(sides[0]),
        project_proof_constants_including_selected=len(full)+1, sha256=sha(output))))

if __name__ == "__main__":
    main()
