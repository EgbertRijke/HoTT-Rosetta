# Building and publishing the website

The website follows agda-unimath's pipeline:

1. Agda checks `rosetta-book/all.lagda.md` and produces linked, highlighted
   Markdown with its HTML backend.
2. Python generates the sidebar from the imports in `all.lagda.md` and each
   chapter, and stages the website assets.
3. mdBook renders `book/html/`, using the same theme, search, Catppuccin colors,
   page table of contents, KaTeX, and local-link checker as agda-unimath.
4. GitHub Actions uploads the HTML artifact and deploys it to GitHub Pages.

## Publish on GitHub

1. Commit these files to the Rosetta repository, including the `.github/`
   directory.
2. In the repository's **Settings → Pages → Build and deployment**, select
   **GitHub Actions** as the source.
3. Push to the repository's default branch. Alternatively, run **Build and
   deploy book website** from the Actions tab, choosing the default branch.
4. The deployment job reports the website URL. If the `github-pages`
   environment has branch protection rules, allow the default branch there.

No personal access token, additional repository secret, external Agda library,
or branch containing generated HTML is needed. The workflow discovers the
repository and default branch automatically. Project sites, user/organization
sites, and custom domains use relative asset links; there is no hard-coded
`/rosetta/` prefix or repository owner to replace.

Pull requests run **HoTT Rosetta CI**, which typechecks the book and checks the
website's structure and local links. They do not deploy. The Pages workflow
builds and deploys only from the default branch. Both workflows use the same
Agda interface cache and pinned tool versions.

GitHub's reference:
[Using custom workflows with GitHub Pages](https://docs.github.com/en/pages/getting-started-with-github-pages/using-custom-workflows-with-github-pages).

## Local prerequisites

- Agda **2.8.0** (the same version as the supplied agda-unimath setup).
- Python **3.10 or later**, GNU Make, and Rust/Cargo for installing mdBook tools.
- mdBook **0.4.52**, mdbook-linkcheck **0.7.7**, mdbook-katex **0.9.0**,
  mdbook-pagetoc **0.2.2**, and mdbook-catppuccin **1.2.0**.
The tool versions are declared in the `Makefile`. GitHub Actions reads the
same versions using `make website-toolchain`.

From the repository root:

```sh
agda --setup
make install-website-dev
make check
make website
```

Open `book/html/index.html`, or serve it locally:

```sh
make serve-website
```

This starts mdBook on port 8080. After changing Agda sources, stop the server
and rerun `make serve-website` to regenerate the highlighted pages.

For a fast prose-only preview that does not invoke Agda:

```sh
make SKIPAGDA=1 website
```

These previews retain fenced Agda code but lack Agda's semantic highlighting
and definition links. They do not typecheck the formalizations. CI runs the
independent `make check` job as well as this fast link check.

For a link check without the HTML renderer:

```sh
MDBOOK_OUTPUT='{"linkcheck":{}}' make SKIPAGDA=1 website
```

Repository and edit buttons are set automatically in the Pages build. To show
them in a local build, use your repository URL and branch:

```sh
export MDBOOK_OUTPUT__HTML__GIT_REPOSITORY_URL=https://github.com/OWNER/REPOSITORY
export MDBOOK_OUTPUT__HTML__EDIT_URL_TEMPLATE='https://github.com/OWNER/REPOSITORY/edit/main/{path}'
make website
```

## Adding content

Add a `.lagda.md` module to `rosetta-book/`, with a level-one Markdown title and
a matching Agda module declaration. Import new sections and exercises from
their chapter, in reading order. Import new chapters from `all.lagda.md`.
The sidebar is regenerated from those imports, so chapter 10 follows chapter 9
and exercise 10 follows exercise 9. It is not sorted alphabetically.

`make check-sources` rejects missing imports, duplicate sidebar entries,
orphaned sections/exercises, and files not reachable from `all.lagda.md`.
`make test-website` exercises the navigation and link transformations.

The website build translates relative `.lagda.md` prose links into `.md`
links before mdBook renders them, preserving anchors. The benchmark's plain
source-file lists become clickable links in the generated website. One
inherited `foundation-core.sections.md` link is redirected to agda-unimath.
Shortcut links naming existing modules also become clickable links. These
transformations affect only generated pages.

## Files and cleanup

- `book.toml`: mdBook configuration.
- `Makefile`: local build commands.
- `scripts/`: source checks, navigation, staging, and Agda color generation.
- `website/`: the reused theme, styles, scripts, favicon assets, and license.
- `.github/actions/`: shared Agda and mdBook setup.
- `.github/workflows/ci.yaml`: pull-request validation.
- `.github/workflows/pages.yaml`: default-branch build and deployment.

`make clean-website` removes generated website files; `make clean` also removes
the Agda interface cache. Generated output is ignored by Git.

The agda-unimath-specific contributor metadata, concept index, bibliography
preprocessor, dependency graph artwork, and analytics are not configured for
Rosetta. They are not needed to render the book content.
