#!/usr/bin/env python3
"""Copy literate Markdown for a fast, explicitly untypechecked prose preview."""

import argparse
from pathlib import Path
import shutil
from book_sources import SOURCE, SUFFIX, module_name


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("output", type=Path)
    args = parser.parse_args()
    args.output.mkdir(parents=True, exist_ok=True)
    for source in SOURCE.glob("*" + SUFFIX):
        shutil.copyfile(source, args.output / (module_name(source) + ".md"))
