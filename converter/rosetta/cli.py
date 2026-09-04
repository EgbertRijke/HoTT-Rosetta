"""Command-line interface designed for non-programmer collaborators."""

import argparse
import json
import shutil
import subprocess
import sys
from pathlib import Path

from .latex import inventory, subsection_body
from .pandoc import PandocUnavailable, latex_to_gfm
from .diagnostics import repository_checks
from .agda_manifest import load_manifest, verify_block_source
from .audit import audit_agda_sources, audit_sections
from .render import render_section
from .compare import (
    MIN_PROSE_SIMILARITY,
    candidate_raw_tex_commands,
    comparison_issues,
    compare_section,
    pending_diagram_count,
)
from .generate import (
    agda_typecheck_options,
    candidate_chapter,
    candidate_exercise,
    candidate_section,
    typecheck_candidate,
    write_candidate,
    write_support_files,
)
from .file_registry import registered_filename
from .layout import rosetta_directory
from .review import discover_diagram_reviews, update_diagram_review
from .agda_review import discover_agda_reviews
from .review_web import serve_review
from .missing_agda import load_agda_coverage
from .agda_typecheck import prepare_candidate_dependencies


ROOT = Path(__file__).resolve().parents[2]


def command_inventory(as_json: bool) -> int:
    sections = inventory(ROOT / "book")
    records = [
        {
            "number": item.number,
            "title": item.title,
            "source": str(item.path.relative_to(ROOT)),
            "subsections": len(item.subsections),
            "exercises": item.exercise_count,
        }
        for item in sections
    ]
    if as_json:
        print(json.dumps(records, indent=2, ensure_ascii=False))
    else:
        print(f"Found {len(records)} globally numbered sections:\n")
        for item in records:
            print(
                f"{item['number']:>2}. {item['title']} "
                f"({item['subsections']} subsections, {item['exercises']} exercises)"
            )
    return 0


def command_prototype(section: int, subsection: int) -> int:
    sections = inventory(ROOT / "book")
    if section < 1 or section > len(sections):
        print(f"Section must be between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    selected = sections[section - 1]
    try:
        markdown = render_section(selected.path, section, subsection)
    except (IndexError, PandocUnavailable, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(markdown.rstrip())
    return 0


def command_check(strict: bool = False) -> int:
    findings = repository_checks(ROOT)
    blocks = []
    try:
        blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
        from .diagnostics import Diagnostic

        findings.append(Diagnostic("ok", f"Agda manifest is valid ({len(blocks)} blocks)."))
        complete_files = load_agda_coverage(ROOT)
        findings.append(
            Diagnostic("ok", f"Agda coverage data is valid ({len(complete_files)} complete files).")
        )
        source_errors = [
            error
            for block in blocks
            for error in verify_block_source(block, ROOT / "external" / "agda-unimath")
        ]
        if source_errors:
            findings.append(Diagnostic("error", "\n".join(source_errors)))
        elif blocks:
            exact = sum(block.provenance_kind == "exact" for block in blocks)
            adapted = sum(block.provenance_kind == "adapted" for block in blocks)
            handwritten = sum(block.provenance_kind == "handwritten" for block in blocks)
            findings.append(
                Diagnostic(
                    "ok",
                    f"Agda sources verified ({exact} exact, {adapted} adapted, "
                    f"{handwritten} handwritten/local).",
                )
            )
    except (OSError, ValueError, json.JSONDecodeError) as error:
        from .diagnostics import Diagnostic

        findings.append(Diagnostic("error", f"Invalid Agda manifest or coverage data: {error}"))
    for finding in findings:
        print(f"[{finding.level.upper()}] {finding.message}")
    failed = any(item.level == "error" for item in findings)
    if strict:
        existing_blocks, _ = audit_agda_sources(ROOT, 3, 6)
        uncurated = max(0, len(existing_blocks) - len(blocks))
        reviews = discover_diagram_reviews(ROOT)
        pending = sum(item.item.state != "approved" for item in reviews)
        agda_reviews = discover_agda_reviews(ROOT)
        agda_pending = sum(item.state != "approved" for item in agda_reviews)
        if uncurated:
            print(f"[ERROR] Strict provenance check: {uncurated} Agda blocks are not in the curated manifest.")
        if pending:
            print(f"[ERROR] Strict review check: {pending} diagram drafts are not approved.")
        if agda_pending:
            print(f"[ERROR] Strict review check: {agda_pending} Agda blocks are not approved.")
        failed = failed or bool(uncurated or pending or agda_pending)
    return 1 if failed else 0


def command_audit(first: int, last: int, as_json: bool) -> int:
    try:
        records = audit_sections(ROOT, first, last)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 2
    if as_json:
        print(json.dumps([record.to_dict() for record in records], indent=2))
        return 0
    print("Section  File  Items       Agda blocks  Prose  Agda coverage")
    for record in records:
        item_summary = f"{record.found_numbered_items}/{record.expected_numbered_items}"
        print(
            f"{record.chapter:>2}.{record.subsection:<4} "
            f"{'yes' if record.file_present else 'no ':<5} "
            f"{item_summary:<11} {record.substantive_agda_blocks:<12} "
            f"{record.prose_coverage:<7} {record.agda_coverage}"
        )
        if record.missing_item_numbers:
            print(f"         Missing item headings: {', '.join(record.missing_item_numbers)}")
    print("\n'unknown' means the audit has not established completeness; it does not mean failure.")
    return 0


def command_compare(section: int, subsection: int, as_json: bool) -> int:
    sections = inventory(ROOT / "book")
    if section < 1 or section > len(sections):
        print(f"Chapter must be between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    expected = rosetta_directory(ROOT) / registered_filename(
        ROOT, "section", section, subsection
    )
    if not expected.is_file():
        print(
            f"Generated file is missing for Section {section}.{subsection}.",
            file=sys.stderr,
        )
        return 2
    try:
        generated = render_section(sections[section - 1].path, section, subsection)
        result = compare_section(generated, expected, ROOT)
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    if as_json:
        print(json.dumps(result.to_dict(), indent=2))
    else:
        print(f"Fixture: {result.destination}")
        print(f"Prose similarity: {result.prose_similarity:.1%}")
        print(
            f"Matching headings: {result.matching_headings}/{result.expected_headings}"
        )
        print(
            "Display math fences: "
            f"generated {result.generated_text_fences}, "
            f"fixture {result.expected_text_fences}"
        )
        print(f"Unresolved references: {result.unresolved_references}")
        print(
            "Raw TeX commands outside code: "
            + (", ".join(result.raw_tex_commands) or "none")
        )
    return 0


def command_compare_range(first: int, last: int, as_json: bool) -> int:
    sections = inventory(ROOT / "book")
    if first < 1 or last > len(sections) or first > last:
        print(f"Chapter range must lie between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    records = []
    missing = []
    try:
        for section in sections[first - 1 : last]:
            for subsection in range(1, len(section.subsections) + 1):
                expected = rosetta_directory(ROOT) / registered_filename(
                    ROOT, "section", section.number, subsection
                )
                if not expected.is_file():
                    missing.append(f"{section.number}.{subsection}")
                    continue
                generated = render_section(
                    section.path, section.number, subsection
                )
                result = compare_section(generated, expected, ROOT)
                record = result.to_dict()
                record["issues"] = comparison_issues(result)
                records.append(record)
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    average = (
        round(sum(item["prose_similarity"] for item in records) / len(records), 4)
        if records
        else 0.0
    )
    ready = not missing and all(not item["issues"] for item in records)
    report = {
        "chapters": [first, last],
        "sections_compared": len(records),
        "missing_fixtures": missing,
        "minimum_prose_similarity": MIN_PROSE_SIMILARITY,
        "average_prose_similarity": average,
        "high_fidelity_ready": ready,
        "comparisons": records,
    }
    if as_json:
        print(json.dumps(report, indent=2))
        return 0
    problems = [item for item in records if item["issues"]]
    print(f"Compared {len(records)} sections in Chapters {first}--{last}.")
    print(f"Average prose similarity: {average:.1%}")
    print(f"High-fidelity target: prose at least {MIN_PROSE_SIMILARITY:.0%}, "
          "matching headings and displays, and no unfinished notation.")
    print(f"Sections needing work: {len(problems) + len(missing)}")
    for item in problems:
        print(f"  {item['destination']}: {', '.join(item['issues'])}")
    for number in missing:
        print(f"  Section {number}: generated file missing")
    print("High-fidelity ready: " + ("yes" if ready else "no"))
    return 0


def command_candidate(section: int, subsection: int) -> int:
    sections = inventory(ROOT / "book")
    if section < 1 or section > len(sections):
        print(f"Chapter must be between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    try:
        write_support_files(ROOT)
        blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
        filename, document = candidate_section(
            sections[section - 1], subsection, blocks
        )
        destination = write_candidate(ROOT, filename, document)
    except (IndexError, OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(destination.relative_to(ROOT))
    print(f"Candidate written to {rosetta_directory(ROOT).relative_to(ROOT)}/.")
    raw_commands = candidate_raw_tex_commands(document)
    pending_diagrams = pending_diagram_count(document)
    unresolved = document.count("[unresolved reference:")
    unsupported = document.count("unsupported LaTeX environment:")
    if raw_commands or unresolved or unsupported:
        print("Candidate requires further conversion work:")
        if raw_commands:
            print("  Raw TeX commands: " + ", ".join(raw_commands))
        if unresolved:
            print(f"  Unresolved references: {unresolved}")
        if unsupported:
            print(f"  Unsupported environments: {unsupported}")
    if pending_diagrams:
        print(f"Reviewable output: {pending_diagrams} automatic diagram drafts.")
    if not (raw_commands or unresolved or unsupported or pending_diagrams):
        print("No unresolved references, environments, or raw TeX commands detected.")
    return 0


def command_candidate_exercise(section: int, exercise: int) -> int:
    sections = inventory(ROOT / "book")
    try:
        write_support_files(ROOT)
        blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
        filename, document = candidate_exercise(
            ROOT, sections[section - 1], exercise, blocks
        )
        destination = write_candidate(ROOT, filename, document)
    except (IndexError, OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(destination.relative_to(ROOT))
    print(f"Candidate written to {rosetta_directory(ROOT).relative_to(ROOT)}/.")
    return 0


def command_candidate_chapter(section: int) -> int:
    sections = inventory(ROOT / "book")
    try:
        write_support_files(ROOT)
        filename, document = candidate_chapter(ROOT, sections[section - 1])
        destination = write_candidate(ROOT, filename, document)
    except (IndexError, OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(destination.relative_to(ROOT))
    print(f"Candidate written to {rosetta_directory(ROOT).relative_to(ROOT)}/.")
    return 0


def command_convert(first: int, last: int) -> int:
    """Generate a complete active Rosetta tree."""
    sections = inventory(ROOT / "book")
    if first < 1 or last > len(sections) or first > last:
        print(f"Chapter range must lie between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
    written = 0
    try:
        write_support_files(ROOT)
        for section in sections[first - 1:last]:
            for subsection in range(1, len(section.subsections) + 1):
                filename, document = candidate_section(section, subsection, blocks)
                write_candidate(ROOT, filename, document)
                written += 1
            for exercise in range(1, section.exercise_count + 1):
                filename, document = candidate_exercise(ROOT, section, exercise, blocks)
                write_candidate(ROOT, filename, document)
                written += 1
            filename, document = candidate_chapter(ROOT, section)
            write_candidate(ROOT, filename, document)
            written += 1
    except (OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    print(
        f"Generated {written} candidates under "
        f"{rosetta_directory(ROOT).relative_to(ROOT)}/."
    )
    return 0


def command_typecheck_candidate(section: int, subsection: int) -> int:
    sections = inventory(ROOT / "book")
    if section < 1 or section > len(sections):
        print(f"Chapter must be between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    try:
        blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
        filename, document = candidate_section(
            sections[section - 1], subsection, blocks
        )
        document, _ = prepare_candidate_dependencies(ROOT, document, blocks)
        returncode, output, staged = typecheck_candidate(
            ROOT, filename, document
        )
    except (IndexError, OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    if output.strip():
        print(output.rstrip())
    if returncode:
        print(f"Candidate typecheck failed: {staged.relative_to(ROOT)}", file=sys.stderr)
        return 1
    print(f"Candidate typecheck passed: {staged.relative_to(ROOT)}")
    return 0


def command_typecheck_exercise_candidate(section: int, exercise: int) -> int:
    sections = inventory(ROOT / "book")
    if section < 1 or section > len(sections):
        print(f"Chapter must be between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    try:
        blocks = load_manifest(ROOT / "data" / "agda-blocks.json")
        filename, document = candidate_exercise(
            ROOT, sections[section - 1], exercise, blocks
        )
        document, _ = prepare_candidate_dependencies(ROOT, document, blocks)
        returncode, output, staged = typecheck_candidate(ROOT, filename, document)
    except (IndexError, OSError, ValueError, RuntimeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    if output.strip():
        print(output.rstrip())
    if returncode:
        print(f"Exercise candidate typecheck failed: {staged.relative_to(ROOT)}", file=sys.stderr)
        return 1
    print(f"Exercise candidate typecheck passed: {staged.relative_to(ROOT)}")
    return 0


def command_typecheck_all(first: int, last: int) -> int:
    """Typecheck aggregate generated chapters from the configured product."""

    sections = inventory(ROOT / "book")
    if first < 1 or last > len(sections) or first > last:
        print(f"Chapter range must lie between 1 and {len(sections)}.", file=sys.stderr)
        return 2
    agda = shutil.which("agda")
    if agda is None:
        print("Agda is not installed or not on PATH.", file=sys.stderr)
        return 2
    directory = rosetta_directory(ROOT)
    for section in sections[first - 1:last]:
        filename = registered_filename(ROOT, "chapter", section.number)
        path = directory / filename
        if not path.is_file():
            print(f"Generated chapter is missing: {path.relative_to(ROOT)}", file=sys.stderr)
            return 1
        print(f"Typechecking Chapter {section.number}: {filename}", flush=True)
        process = subprocess.run(
            [
                agda,
                *agda_typecheck_options(agda),
                "-i",
                str(directory),
                str(path),
            ],
            cwd=ROOT,
            text=True,
            check=False,
        )
        if process.returncode:
            return process.returncode
    print(f"Aggregate Chapters {first}--{last} typecheck.")
    return 0


def command_agda_source_audit(first: int, last: int, as_json: bool) -> int:
    try:
        blocks, evidence = audit_agda_sources(ROOT, first, last)
    except (OSError, ValueError) as error:
        print(str(error), file=sys.stderr)
        return 2
    records = [
        {
            "destination": block.destination,
            "item_id": block.item_id,
            "start_line": block.start_line,
            "source_category": evidence[(block.destination, block.start_line)].category,
            "sources": evidence[(block.destination, block.start_line)].sources,
            "exact_sources": (
                evidence[(block.destination, block.start_line)].sources
                if evidence[(block.destination, block.start_line)].category
                == "exact-full"
                else []
            ),
        }
        for block in blocks
    ]
    if as_json:
        print(json.dumps(records, indent=2))
        return 0
    counts = {
        category: sum(record["source_category"] == category for record in records)
        for category in (
            "exact-full", "exact-excerpts", "adapted-normalized", "handwritten-local"
        )
    }
    print(f"Exact full blocks: {counts['exact-full']}/{len(records)}")
    print(f"Exact combined excerpts: {counts['exact-excerpts']}/{len(records)}")
    print(f"Adapted (normalization evidence): {counts['adapted-normalized']}/{len(records)}")
    print(f"Handwritten/local (no upstream match): {counts['handwritten-local']}/{len(records)}")
    for record in records:
        status = record["source_category"]
        print(
            f"{status:<18} {record['destination']}:{record['start_line']} "
            f"{record['item_id'] or '(no numbered item)'}"
        )
        for source in record["sources"]:
            print(f"  {source}")
    return 0


def command_review(
    as_json: bool, approve: str = None, comment: list = None,
    web: bool = False, port: int = 8765,
) -> int:
    """Report reviewable diagram drafts without changing any files."""

    try:
        if web:
            serve_review(ROOT, port=port)
            return 0
        if approve:
            path = update_diagram_review(ROOT, approve, state="approved")
            print(f"Approved diagram {approve} in {path.relative_to(ROOT)}.")
        if comment:
            stable_id, text = comment
            path = update_diagram_review(ROOT, stable_id, comment=text)
            print(f"Comment saved for diagram {stable_id} in {path.relative_to(ROOT)}.")
        records = discover_diagram_reviews(ROOT)
        agda_records = discover_agda_reviews(ROOT)
    except (OSError, ValueError, json.JSONDecodeError) as error:
        print(str(error), file=sys.stderr)
        return 2
    if as_json:
        print(
            json.dumps(
                {
                    "agda": [record.to_dict() for record in agda_records],
                    "diagrams": [record.to_dict() for record in records],
                },
                indent=2,
                ensure_ascii=False,
            )
        )
        return 0
    agda_pending = sum(record.state == "pending" for record in agda_records)
    agda_needs_review = sum(
        record.state == "needs-further-review" for record in agda_records
    )
    agda_approved = sum(record.state == "approved" for record in agda_records)
    agda_stale = sum(record.state == "stale" for record in agda_records)
    print(
        f"Agda reviews: {len(agda_records)} total, {agda_pending} pending, "
        f"{agda_needs_review} need further review, "
        f"{agda_approved} approved, {agda_stale} stale."
    )
    print("Run 'python3 rosetta.py review --web' for side-by-side review.")
    pending = sum(record.item.state == "pending" for record in records)
    approved = sum(record.item.state == "approved" for record in records)
    stale = sum(record.item.state == "stale" for record in records)
    paired = sum(bool(record.item.source) for record in records)
    print(
        f"Diagram reviews: {len(records)} total, {pending} pending, "
        f"{approved} approved, {stale} stale."
    )
    print(f"Original sources paired: {paired}/{len(records)}.")
    if not records:
        print("Generate section candidates first with 'python3 rosetta.py candidate N M'.")
        return 0
    for record in records:
        print(
            f"{record.item.state:<8} {record.item.stable_id} "
            f"{record.destination}: {record.item.description} "
            f"({len(record.item.comments)} comments)"
        )
    return 0


def build_parser() -> argparse.ArgumentParser:
    parser = argparse.ArgumentParser(
        prog="rosetta.py",
        description="Convert and check the HoTT Rosetta book sources.",
    )
    subcommands = parser.add_subparsers(dest="command", required=True)
    inventory_parser = subcommands.add_parser(
        "inventory", help="list the book sections in source order"
    )
    inventory_parser.add_argument("--json", action="store_true", help="print JSON")
    prototype = subcommands.add_parser(
        "prototype", help="preview Pandoc conversion of one subsection"
    )
    prototype.add_argument("section", type=int, help="global section number")
    prototype.add_argument("subsection", type=int, help="subsection number")
    check = subcommands.add_parser("check", help="check tools, sources, imports, and data")
    check.add_argument("--strict", action="store_true", help="also require provenance and optional reviews")
    audit = subcommands.add_parser(
        "audit", help="inspect evidence about existing section translations"
    )
    audit.add_argument("--from", dest="first", type=int, default=3)
    audit.add_argument("--to", dest="last", type=int, default=6)
    audit.add_argument("--json", action="store_true", help="print JSON")
    compare = subcommands.add_parser(
        "compare", help="measure a regenerated section against its active file"
    )
    compare.add_argument("section", type=int)
    compare.add_argument("subsection", type=int)
    compare.add_argument("--json", action="store_true", help="print JSON")
    compare_range = subcommands.add_parser(
        "compare-range", help="summarize regenerated sections against active files"
    )
    compare_range.add_argument("--from", dest="first", type=int, default=3)
    compare_range.add_argument("--to", dest="last", type=int, default=17)
    compare_range.add_argument("--json", action="store_true", help="print JSON")
    candidate = subcommands.add_parser(
        "candidate", help="write one section under the configured Rosetta directory"
    )
    candidate.add_argument("section", type=int)
    candidate.add_argument("subsection", type=int)
    candidate_exercise = subcommands.add_parser(
        "candidate-exercise", help="write one exercise under the configured Rosetta directory"
    )
    candidate_exercise.add_argument("section", type=int)
    candidate_exercise.add_argument("exercise", type=int)
    candidate_chapter = subcommands.add_parser(
        "candidate-chapter", help="write one chapter under the configured Rosetta directory"
    )
    candidate_chapter.add_argument("section", type=int)
    convert = subcommands.add_parser(
        "convert", help="generate section, exercise, and chapter candidates safely"
    )
    convert.add_argument("--from", dest="first", type=int, default=3)
    convert.add_argument("--to", dest="last", type=int, default=22)
    candidate_check = subcommands.add_parser(
        "typecheck-candidate",
        help="typecheck generated content under a non-conflicting temporary module",
    )
    candidate_check.add_argument("section", type=int)
    candidate_check.add_argument("subsection", type=int)
    exercise_check = subcommands.add_parser(
        "typecheck-exercise-candidate",
        help="typecheck one generated exercise under a temporary module name",
    )
    exercise_check.add_argument("section", type=int)
    exercise_check.add_argument("exercise", type=int)
    typecheck_all = subcommands.add_parser(
        "typecheck-all", help="typecheck aggregate generated chapter modules",
    )
    typecheck_all.add_argument("--from", dest="first", type=int, default=1)
    typecheck_all.add_argument("--to", dest="last", type=int, default=22)
    source_audit = subcommands.add_parser(
        "agda-source-audit",
        help="find existing section blocks copied verbatim from agda-unimath",
    )
    source_audit.add_argument("--from", dest="first", type=int, default=3)
    source_audit.add_argument("--to", dest="last", type=int, default=6)
    source_audit.add_argument("--json", action="store_true")
    review = subcommands.add_parser(
        "review", help="list generated diagrams awaiting optional human review"
    )
    review.add_argument("--json", action="store_true", help="include drafts and sources")
    review.add_argument("--web", action="store_true", help="start the local browser interface")
    review.add_argument("--port", type=int, default=8765, help="browser interface port")
    actions = review.add_mutually_exclusive_group()
    actions.add_argument("--approve", metavar="DIAGRAM_ID")
    actions.add_argument(
        "--comment", nargs=2, metavar=("DIAGRAM_ID", "TEXT")
    )
    return parser


def main(argv=None) -> int:
    arguments = build_parser().parse_args(argv)
    if arguments.command == "inventory":
        return command_inventory(arguments.json)
    if arguments.command == "prototype":
        return command_prototype(arguments.section, arguments.subsection)
    if arguments.command == "check":
        return command_check(arguments.strict)
    if arguments.command == "audit":
        return command_audit(arguments.first, arguments.last, arguments.json)
    if arguments.command == "compare":
        return command_compare(arguments.section, arguments.subsection, arguments.json)
    if arguments.command == "compare-range":
        return command_compare_range(arguments.first, arguments.last, arguments.json)
    if arguments.command == "candidate":
        return command_candidate(arguments.section, arguments.subsection)
    if arguments.command == "candidate-exercise":
        return command_candidate_exercise(arguments.section, arguments.exercise)
    if arguments.command == "candidate-chapter":
        return command_candidate_chapter(arguments.section)
    if arguments.command == "convert":
        return command_convert(arguments.first, arguments.last)
    if arguments.command == "typecheck-candidate":
        return command_typecheck_candidate(arguments.section, arguments.subsection)
    if arguments.command == "typecheck-exercise-candidate":
        return command_typecheck_exercise_candidate(
            arguments.section, arguments.exercise
        )
    if arguments.command == "typecheck-all":
        return command_typecheck_all(arguments.first, arguments.last)
    if arguments.command == "agda-source-audit":
        return command_agda_source_audit(
            arguments.first, arguments.last, arguments.json
        )
    if arguments.command == "review":
        return command_review(
            arguments.json, arguments.approve, arguments.comment,
            arguments.web, arguments.port,
        )
    return 2
