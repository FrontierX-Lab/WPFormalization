#!/usr/bin/env python3
"""Check numbered results against the original paper and the declaration registry."""
from pathlib import Path
import collections
import hashlib
import json
import re
import subprocess

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "source/arxiv-v3"
REQUESTED_PDF = ROOT / "source/paper.pdf"
EXPECTED_PDF_SHA256 = "798c1f564636052b1904206538d5be855f19ea1e5da4f41df88a479c2cc8b4cc"
assert hashlib.sha256(REQUESTED_PDF.read_bytes()).hexdigest() == EXPECTED_PDF_SHA256
(ROOT / "_out/audit").mkdir(parents=True, exist_ok=True)


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


targets = json.loads((ROOT / "audit/targets.json").read_text())
by_label = {r["label"]: r for r in targets}
status = json.loads((ROOT / "audit/proof-status.json").read_text())
status_by_label = {r["label"]: r for r in status["targetRecords"]}
declarations = status["declarations"]
aux = (SOURCE / "labels.aux").read_text()
aux_labels = {
    m[1]: {"number": m[2], "page": int(m[3])}
    for m in re.finditer(r"\\newlabel\{([^}]+)\}\{\{([^}]+)\}\{(\d+)\}", aux)
}
theorem_pattern = re.compile(
    r"\\begin\{(theorem|lemma|proposition|corollary)\}(.*?)\\end\{\1\}", re.S
)
numbered = []
missing_labels = []
mapping_mismatches = []
aux_page_differences = []
pdf_pages = (ROOT / "source/paper.txt").read_text().split("\f")
for path in sorted(SOURCE.glob("*.tex")):
    text = path.read_text()
    for match in theorem_pattern.finditer(text):
        labels = re.findall(r"\\label\{([^}]+)\}", match[2])
        label = labels[0] if labels else None
        record = {
            "kind": match[1],
            "source": str(path.relative_to(ROOT)),
            "line": text.count("\n", 0, match.start()) + 1,
            "label": label,
            "aux": aux_labels.get(label),
            "registered": label in by_label,
        }
        numbered.append(record)
        if label not in by_label:
            missing_labels.append(record)
        elif record["aux"]:
            registered = by_label[label]
            heading_pattern = r"^[ \t]*" + match[1].title() + r"\s+" + re.escape(
                registered["number"]) + r"(?=\s*(?:[.(]|$))"
            actual_pages = [i + 1 for i, p in enumerate(pdf_pages)
                            if re.search(heading_pattern, p, re.M)]
            record["pdfHeadingPages"] = actual_pages
            if registered["number"] != record["aux"]["number"] or registered["page"] not in actual_pages:
                mapping_mismatches.append({"source": record,
                                           "registeredNumber": registered["number"],
                                           "registeredPage": registered["page"]})
            if registered["page"] != record["aux"]["page"]:
                aux_page_differences.append({"label": label,
                                             "auxLabelPage": record["aux"]["page"],
                                             "registeredStartPage": registered["page"],
                                             "pdfHeadingPages": actual_pages})

proofless_paper_labels = []
for row in targets:
    if row["classification"] != "paper-new":
        continue
    assoc = status_by_label.get(row["label"], {}).get("declarations", [])
    if not any(declarations.get(n, {}).get("kind") in ("theorem", "lemma") for n in assoc):
        proofless_paper_labels.append(row["label"])

math_hash = hashlib.sha256()
for path in sorted((ROOT / "WPFormalization").rglob("*.lean")):
    math_hash.update(str(path.relative_to(ROOT)).encode())
    math_hash.update(path.read_bytes())

fresh_pdf_text = subprocess.check_output(
    ["pdftotext", "-layout", str(REQUESTED_PDF), "-"], text=True
)
cached_pdf_text = (ROOT / "source/paper.txt").read_text()
report = {
    "scope": "Independent source discovery, PDF identity, registered declaration presence, and theorem/declaration mapping. No claim that counts or theorem presence prove semantic fidelity.",
    "pinnedPdfSha256": digest(REQUESTED_PDF),
    "copiedPdfSha256": digest(ROOT / "source/paper.pdf"),
    "pinnedPdfHashMatches": digest(REQUESTED_PDF) == EXPECTED_PDF_SHA256,
    "cachedTextExactlyMatchesFreshExtraction": cached_pdf_text == fresh_pdf_text,
    "sourceHash": math_hash.hexdigest(),
    "compiledReportSourceHash": status["sourceHash"],
    "compiledReportMatchesCurrentMath": math_hash.hexdigest() == status["sourceHash"],
    "discoveredNumberedResults": len(numbered),
    "numberedKindCounts": dict(collections.Counter(r["kind"] for r in numbered)),
    "missingNumberedSourceResults": missing_labels,
    "numberedSourceMappingMismatches": mapping_mismatches,
    "auxLabelPageVsPdfStartPageDifferences": aux_page_differences,
    "numberedSourceResults": numbered,
    "registryTargetCount": len(targets),
    "registryClassificationCounts": dict(collections.Counter(r["classification"] for r in targets)),
    "paperNewLabelsWithoutTheoremInCompiledReport": proofless_paper_labels,
    "limits": [
        "The source theorem-environment scan does not discover mathematical claims in prose or unnumbered display equations.",
        "Presence of a theorem association does not certify that all conjuncts, quantifiers, domains, constants or remainder estimates match the source.",
        "The compiled report must be freshly regenerated after target/Blueprint changes; matching the math hash alone does not prove that target records are current.",
        "Unregistered explicit assumptions are not excluded by the finite recognized-interface and paper-goal lists in the main audit.",
    ],
}
(ROOT / "_out/audit/paper-coverage.json").write_text(json.dumps(report, ensure_ascii=False, indent=2) + "\n")
summary = {k: v for k, v in report.items()
           if k not in ("numberedSourceResults", "limits", "scope", "auxLabelPageVsPdfStartPageDifferences")}
print(json.dumps(summary, ensure_ascii=False, indent=2))

assert report["pinnedPdfHashMatches"] and report["cachedTextExactlyMatchesFreshExtraction"]
assert report["compiledReportMatchesCurrentMath"]
assert not missing_labels and not mapping_mismatches and not proofless_paper_labels
assert len(numbered) == 57
