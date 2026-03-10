import fs from 'node:fs';
import path from 'node:path';
import MarkdownIt from 'markdown-it';
import texmath from 'markdown-it-texmath';
import katex from 'katex';

// const inputFile = process.argv[2] || 'Simplex.md';
// const outputFile = process.argv[3] || inputFile.replace(/\.md$/, '.html');

const inputFile = 'Simplex.md';
const outputFile = 'index.html';

const md = new MarkdownIt({
  html: true,
  linkify: true,
  typographer: true,
});

md.use(texmath, {
  engine: katex,
  delimiters: 'dollars',
  katexOptions: { throwOnError: false },
});

// Anchorable headings: generate GitHub-style slug IDs
const slugCounts = {};
md.renderer.rules.heading_open = (tokens, idx) => {
  const tag = tokens[idx].tag;
  // Collect text content from inline children, stripping HTML/math markup
  const inline = tokens[idx + 1];
  const rawText = inline.children
    ? inline.children.map(t => t.type === 'text' || t.type === 'code_inline' ? t.content : '').join('')
    : inline.content;
  let slug = rawText
    .toLowerCase()
    .trim()
    .replace(/[^\w\s-]/g, '')
    .replace(/\s+/g, '-');
  // Deduplicate slugs
  if (slug in slugCounts) {
    slugCounts[slug]++;
    slug = `${slug}-${slugCounts[slug]}`;
  } else {
    slugCounts[slug] = 0;
  }
  return `<${tag} id="${slug}"><a class="anchor" href="#${slug}">#</a> `;
};

let input = fs.readFileSync(inputFile, 'utf8');

// Preprocess: inside display math ($$...$$), replace $...$ within \text{...}
// with the equivalent \text{}-closing-and-reopening form, so that the markdown
// parser doesn't consume the dollar signs as inline math delimiters.
input = input.replace(/\$\$\n([\s\S]*?)\n\$\$/g, (_match, inner) => {
  const fixed = inner.replace(
    /\\text\{([^}]*)\}/g,
    (_m, textContent) => {
      const replaced = textContent.replace(/\$([^$]+)\$/g, '}$1\\text{');
      return `\\text{${replaced}}`;
    }
  );
  return `$$\n${fixed}\n$$`;
});

const body = md.render(input);

const katexDir = path.dirname(new URL(import.meta.resolve('katex')).pathname);
const katexPkg = JSON.parse(fs.readFileSync(path.join(katexDir, '..', 'package.json'), 'utf8'));
const katexVersion = katexPkg.version;
const katexCdnCss = `https://cdn.jsdelivr.net/npm/katex@${katexVersion}/dist/katex.min.css`;

const html = `<!doctype html>
<html>
<head>
  <meta charset="utf-8" />
  <title>${path.basename(inputFile, '.md')}</title>
  <link rel="stylesheet" href="${katexCdnCss}" crossorigin="anonymous" />
  <style>
    body {
      padding: 0 26px;
      margin: 0;
      max-width: 882px;
      margin: 0 auto;
      font-family: -apple-system, BlinkMacSystemFont, "Segoe WPC", "Segoe UI", system-ui, "Ubuntu", "Droid Sans", sans-serif;
      font-size: 14px;
      line-height: 1.6;
      color: #333;
      background: #fff;
      word-wrap: break-word;
    }
    h1 { font-size: 2em; border-bottom: 1px solid #eee; padding-bottom: .3em; margin-top: 0; }
    h2 { font-size: 1.5em; border-bottom: 1px solid #eee; padding-bottom: .3em; }
    h3 { font-size: 1.25em; }
    a { color: #4080d0; text-decoration: none; }
    a:hover { text-decoration: underline; }
    code {
      font-family: "SF Mono", Monaco, Menlo, Consolas, "Ubuntu Mono", "Liberation Mono", "DejaVu Sans Mono", "Courier New", monospace;
      font-size: 1em;
      background: rgba(220,220,220,0.4);
      padding: 1px 4px;
      border-radius: 3px;
    }
    pre { background: #f6f8fa; padding: 16px; overflow: auto; border-radius: 3px; }
    pre code { background: none; padding: 0; }
    blockquote { margin: 0; padding: 0 1em; color: #6a737d; border-left: .25em solid #dfe2e5; }
    table { border-collapse: collapse; width: 100%; margin-bottom: 16px; }
    th, td { border: 1px solid #dfe2e5; padding: 6px 13px; }
    th { background: #f6f8fa; font-weight: 600; }
    tr:nth-child(2n) { background: #f6f8fa; }
    ul, ol { padding-left: 2em; }
    li + li { margin-top: 0.25em; }
    hr { border: none; border-top: 1px solid #eee; }
    img { max-width: 100%; }
    .katex-display { overflow-x: auto; overflow-y: hidden; }
    .anchor { color: #ccc; font-weight: normal; font-size: 0.8em; text-decoration: none; margin-left: -1.2em; padding-right: 0.4em; }
    .anchor:hover { color: #4080d0; text-decoration: none; }
    h1 .anchor, h2 .anchor, h3 .anchor, h4 .anchor { visibility: hidden; }
    h1:hover .anchor, h2:hover .anchor, h3:hover .anchor, h4:hover .anchor { visibility: visible; }

    @media (prefers-color-scheme: dark) {
      body { color: #d4d4d4; background: #1e1e1e; }
      h1, h2 { border-bottom-color: #333; }
      a { color: #4daafc; }
      .anchor { color: #555; }
      .anchor:hover { color: #4daafc; }
      code { background: rgba(255,255,255,0.1); }
      pre { background: #2d2d2d; }
      blockquote { color: #9e9e9e; border-left-color: #444; }
      th, td { border-color: #444; }
      th { background: #2d2d2d; }
      tr:nth-child(2n) { background: #2d2d2d; }
      hr { border-top-color: #333; }
    }
  </style>
</head>
<body>
${body}
</body>
</html>`;

fs.writeFileSync(outputFile, html);
console.log(`Wrote ${outputFile}`);
