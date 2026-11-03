// Map generated website pages back to their repository source files.
const editLink = document.querySelector('.href-git-edit-button');

if (editLink) {
  const filename = editLink.dataset.source;
  const rootFiles = new Set(['BENCHMARK.md']);
  const docFiles = new Set(['HOME.md']);

  let source;

  if (filename === 'index.md') {
    source = 'docs/HOME.md';
  } else if (filename === 'ABOUT.md') {
    source = 'README.md';
  } else if (rootFiles.has(filename)) {
    source = filename;
  } else if (docFiles.has(filename)) {
    source = 'docs/' + filename;
  } else {
    source = 'rosetta-book/' + filename.replace(/\.md$/, '.lagda.md');
  }

  const url = new URL(editLink.href);
  const originalFilename = filename === 'index.md' ? 'HOME.md' : filename;
  const generatedPath = 'book/src/' + originalFilename;
  const suffix = url.pathname.endsWith(generatedPath)
    ? generatedPath
    : originalFilename;

  if (url.pathname.endsWith(suffix)) {
    url.pathname = url.pathname.slice(0, -suffix.length) + source;
    editLink.href = url.href;
  }
}
