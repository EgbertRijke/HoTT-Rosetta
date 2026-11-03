.DEFAULT_GOAL := website

SOURCE_DIR := rosetta-book
MDBOOK_SRC := book/src
AGDA ?= agda
MDBOOK ?= mdbook
PYTHON ?= python3
AGDAHTMLFLAGS ?= --html --html-highlight=auto --html-dir=../$(MDBOOK_SRC) --css=website/css/Agda.css
SKIPAGDA ?=

.PHONY: check check-sources agda-html website-prepare website serve-website clean-website clean install-website-dev test-website

check-sources:
	$(PYTHON) scripts/book_sources.py

check: check-sources
	cd $(SOURCE_DIR) && $(AGDA) all.lagda.md

agda-html: check-sources
	rm -rf $(MDBOOK_SRC)
	mkdir -p $(MDBOOK_SRC)
ifeq ($(SKIPAGDA),1)
	$(PYTHON) scripts/generate_noagda_html.py $(MDBOOK_SRC)
else
	cd $(SOURCE_DIR) && $(AGDA) $(AGDAHTMLFLAGS) all.lagda.md
endif

website-prepare: agda-html
	$(PYTHON) scripts/generate_mdbook_summary.py $(MDBOOK_SRC)/SUMMARY.md
	$(PYTHON) scripts/generate_agda_css.py
	$(PYTHON) scripts/prepare_website.py $(MDBOOK_SRC)

website: website-prepare
	$(MDBOOK) build

serve-website: website-prepare
	$(MDBOOK) serve --port 8080 --open

test-website:
	$(PYTHON) -m unittest discover -s scripts/tests -v

clean-website:
	rm -rf book website/css/Agda-highlight.css

clean: clean-website
	rm -rf $(SOURCE_DIR)/_build scripts/__pycache__ scripts/tests/__pycache__

install-website-dev:
	cargo install mdbook --version 0.4.34 --locked
	cargo install mdbook-linkcheck --version 0.7.7 --locked
	cargo install mdbook-katex --version 0.5.7 --locked
	cargo install mdbook-pagetoc --version 0.1.7 --locked
	cargo install mdbook-catppuccin --version 1.2.0 --locked
