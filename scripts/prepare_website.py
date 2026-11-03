#!/usr/bin/env python3
"""Stage assets and adapt repository links only in generated website files."""

import argparse
from pathlib import Path
import re
import shutil
from urllib.parse import urlsplit, urlunsplit
from book_sources import ROOT, SOURCE, SUFFIX

# This prose link was inherited from agda-unimath; its target isn't in Rosetta.
UPSTREAM_LINKS = {
    "foundation-core.sections.md":
        "https://unimath.github.io/agda-unimath/foundation-core.sections.html",
}


def rewrite_links(text):
    def replace(match):
        target = urlsplit(match[1])
        if target.scheme or target.netloc:
            return match[0]
        path = target.path.removeprefix("rosetta-book/").removeprefix("docs/")
        if path.endswith(".lagda.md"):
            path = path.removesuffix(".lagda.md") + ".md"
        if path == "README.md":
            path = "ABOUT.md"
        path = UPSTREAM_LINKS.get(path, path)
        return "](" + urlunsplit(("", "", path, target.query, target.fragment)) + ")"

    # Markdown links occur in prose; don't alter fenced examples or Agda HTML.
    parts = re.split(r"(^```[^\n]*\n.*?^```[^\n]*$|<pre\b[^>]*>.*?</pre>)",
                     text, flags=re.M | re.S)
    for index in range(0, len(parts), 2):
        parts[index] = re.sub(r"\]\(([^\s)]+)\)", replace, parts[index])
        # Resolve shortcut links such as [`section-3-3-pattern-matching`]
        # when they refer to a module present in this book.
        parts[index] = re.sub(
            r"\[(`([^`]+)`)\](?![\[(])",
            lambda match: f"[{match[1]}]({match[2]}.md)"
            if (SOURCE / (match[2] + SUFFIX)).is_file() else match[0],
            parts[index],
        )
    return "".join(parts)


def prepare(output):
    output.mkdir(parents=True, exist_ok=True)
    for path in (ROOT / "docs").glob("*.md"):
        shutil.copyfile(path, output / path.name)
    # mdBook's index preprocessor renames README.md to index.md. Stage it as
    # ABOUT.md so it cannot override the actual HOME.md landing page.
    shutil.copyfile(ROOT / "README.md", output / "ABOUT.md")
    benchmark = (ROOT / "BENCHMARK.md").read_text(encoding="utf-8")
    benchmark = re.sub(r"(?m)^- (rosetta-book/[^\s]+\.lagda\.md)\s*$",
                       lambda m: f"- [{Path(m[1]).stem.removesuffix('.lagda')}]({m[1]})", benchmark)
    (output / "BENCHMARK.md").write_text(benchmark, encoding="utf-8")
    shutil.copyfile(ROOT / "website/LICENSE-agda-unimath.md", output / "LICENSE-agda-unimath.md")
    for directory in ("css", "js", "images"):
        shutil.copytree(ROOT / "website" / directory, output / "website" / directory, dirs_exist_ok=True)
    for path in output.glob("*.md"):
        path.write_text(rewrite_links(path.read_text(encoding="utf-8")), encoding="utf-8")
    (output / ".nojekyll").touch()


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    prepare(parser.parse_args().output)
