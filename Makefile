.DEFAULT_GOAL := website

SOURCE_DIR := rosetta-book
MDBOOK_SRC := book/src

AGDA ?= agda
MDBOOK ?= mdbook
PYTHON ?= python3

MDBOOK_VERSION := 0.4.52
MDBOOK_LINKCHECK_VERSION := 0.7.7
MDBOOK_KATEX_VERSION := 0.9.0
MDBOOK_PAGETOC_VERSION := 0.2.2
MDBOOK_CATPPUCCIN_VERSION := 1.2.0

AGDAHTMLFLAGS ?= --html --html-highlight=auto --html-dir=../$(MDBOOK_SRC) --css=website/css/Agda.css

SKIPAGDA ?=

.PHONY: check check-sources agda-html website-prepare website
.PHONY: serve-website clean-website clean install-website-dev
.PHONY: test-website website-toolchain check-website-tools

website-toolchain:
	@echo "mdbook=$(MDBOOK_VERSION)"
	@echo "linkcheck=$(MDBOOK_LINKCHECK_VERSION)"
	@echo "katex=$(MDBOOK_KATEX_VERSION)"
	@echo "pagetoc=$(MDBOOK_PAGETOC_VERSION)"
	@echo "catppuccin=$(MDBOOK_CATPPUCCIN_VERSION)"

check-website-tools:
	@actual_version="$$($(MDBOOK) --version 2>/dev/null)"; \
	if [ "$$actual_version" != "mdbook v$(MDBOOK_VERSION)" ]; then \
		echo "Expected mdbook v$(MDBOOK_VERSION); found $${actual_version:-no mdbook executable}." >&2; \
		echo "Run 'make install-website-dev', and put Cargo's bin directory first on PATH." >&2; \
		echo 'For a standard Cargo install: export PATH="$$HOME/.cargo/bin:$$PATH"' >&2; \
		exit 1; \
	fi
	@for tool in mdbook-linkcheck mdbook-katex mdbook-pagetoc mdbook-catppuccin; do \
		command -v "$$tool" >/dev/null 2>&1 || { \
			echo "Missing $$tool. Run 'make install-website-dev'." >&2; \
			exit 1; \
		}; \
	done

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

website-prepare: check-website-tools
	$(MAKE) --no-print-directory agda-html
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
	@command -v cargo >/dev/null 2>&1 || { \
		echo "Install Rust/Cargo first, then rerun 'make install-website-dev'." >&2; \
		exit 1; \
	}
	cargo install mdbook --version "=$(MDBOOK_VERSION)" --locked
	cargo install mdbook-linkcheck --version "=$(MDBOOK_LINKCHECK_VERSION)" --locked
	cargo install mdbook-katex --version "=$(MDBOOK_KATEX_VERSION)" --force
	cargo install mdbook-pagetoc --version "=$(MDBOOK_PAGETOC_VERSION)" --locked
	cargo install mdbook-catppuccin --version "=$(MDBOOK_CATPPUCCIN_VERSION)" --locked
	$(MAKE) --no-print-directory check-website-tools
