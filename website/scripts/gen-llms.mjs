#!/usr/bin/env node
/*
  gen-llms.mjs — emit LLM-readable twins of every built page.

  Runs AFTER `astro build`, over the rendered `dist/` HTML, so the output always
  matches what is actually published (no separate source of truth to drift).

  For each page it writes a clean Markdown twin at the same path:
      dist/idea/index.html   ->  dist/idea.md   (served at https://qiqt.org/idea.md)
      dist/index.html        ->  dist/index.md  (served at https://qiqt.org/index.md)
  and two site-level indexes for AI crawlers:
      dist/llms.txt       — a curated map (title + description + link to each .md)
      dist/llms-full.txt  — every page's Markdown concatenated

  Nav/header-chrome/footer/scripts/styles are stripped; KaTeX is collapsed back to
  its source TeX ($...$). Dependency-free (Node stdlib only) so it needs no install.
*/
import { readdir, readFile, writeFile, stat } from 'node:fs/promises';
import { join, relative, dirname } from 'node:path';
import { fileURLToPath } from 'node:url';

const DIST = join(dirname(fileURLToPath(import.meta.url)), '..', 'dist');
const SITE = 'https://qiqt.org';

// ---- tiny helpers -------------------------------------------------------------

const ENTITIES = {
  '&amp;': '&', '&lt;': '<', '&gt;': '>', '&quot;': '"', '&#39;': "'",
  '&#x27;': "'", '&nbsp;': ' ', '&thinsp;': ' ', '&mdash;': '—', '&ndash;': '–',
  '&hellip;': '…', '&times;': '×', '&middot;': '·', '&rarr;': '→', '&larr;': '←',
  '&uarr;': '↑', '&darr;': '↓', '&harr;': '↔', '&le;': '≤', '&ge;': '≥',
  '&ne;': '≠', '&sup2;': '²', '&sup3;': '³', '&deg;': '°', '&pi;': 'π',
  '&beta;': 'β', '&omega;': 'ω', '&Delta;': 'Δ', '&delta;': 'δ', '&sigma;': 'σ',
  '&Phi;': 'Φ', '&lambda;': 'λ', '&Lambda;': 'Λ', '&rho;': 'ρ', '&xi;': 'ξ',
  '&eta;': 'η', '&kappa;': 'κ', '&star;': '★',
};
function decodeEntities(s) {
  return s
    .replace(/&#(\d+);/g, (_, n) => String.fromCodePoint(+n))
    .replace(/&#x([0-9a-fA-F]+);/g, (_, n) => String.fromCodePoint(parseInt(n, 16)))
    .replace(/&[a-zA-Z][a-zA-Z0-9]*;/g, (m) => (m in ENTITIES ? ENTITIES[m] : m));
}

// Replace each <span class="katex">…</span> with its source TeX ($…$), matching the
// balanced close so nested spans don't break it.
function collapseKatex(html) {
  const OPEN = '<span class="katex">';
  let out = '';
  let i = 0;
  while (true) {
    const start = html.indexOf(OPEN, i);
    if (start === -1) { out += html.slice(i); break; }
    out += html.slice(i, start);
    // walk balanced <span>…</span> from `start`
    let depth = 0, j = start;
    const spanOpen = /<span\b/g, spanClose = /<\/span>/g;
    // simple scan
    let k = start;
    while (k < html.length) {
      const no = html.indexOf('<span', k);
      const nc = html.indexOf('</span>', k);
      if (nc === -1) { k = html.length; break; }
      if (no !== -1 && no < nc) { depth++; k = no + 5; }
      else { depth--; k = nc + 7; if (depth === 0) break; }
    }
    const block = html.slice(start, k);
    const tex = block.match(/<annotation encoding="application\/x-tex">([\s\S]*?)<\/annotation>/);
    out += tex ? ('$' + decodeEntities(tex[1]).trim() + '$') : '';
    i = k;
  }
  return out;
}

function stripToMarkdown(html) {
  let h = html;
  // isolate <body>
  const bm = h.match(/<body[^>]*>([\s\S]*)<\/body>/i);
  if (bm) h = bm[1];
  // drop non-content regions
  h = h.replace(/<script[\s\S]*?<\/script>/gi, '');
  h = h.replace(/<style[\s\S]*?<\/style>/gi, '');
  h = h.replace(/<nav[\s\S]*?<\/nav>/gi, '');
  h = h.replace(/<footer[\s\S]*?<\/footer>/gi, '');
  h = h.replace(/<svg[\s\S]*?<\/svg>/gi, '');
  // KaTeX -> $tex$
  h = collapseKatex(h);
  h = h.replace(/<span class="katex-mathml">[\s\S]*?<\/span>/gi, '');
  // block elements -> markdown markers
  h = h.replace(/<h1[^>]*>([\s\S]*?)<\/h1>/gi, (_, t) => `\n\n# ${inline(t)}\n\n`);
  h = h.replace(/<h2[^>]*>([\s\S]*?)<\/h2>/gi, (_, t) => `\n\n## ${inline(t)}\n\n`);
  h = h.replace(/<h3[^>]*>([\s\S]*?)<\/h3>/gi, (_, t) => `\n\n### ${inline(t)}\n\n`);
  h = h.replace(/<h4[^>]*>([\s\S]*?)<\/h4>/gi, (_, t) => `\n\n#### ${inline(t)}\n\n`);
  h = h.replace(/<li[^>]*>([\s\S]*?)<\/li>/gi, (_, t) => `\n- ${inline(t)}`);
  h = h.replace(/<pre[^>]*>([\s\S]*?)<\/pre>/gi, (_, t) =>
    `\n\n\`\`\`\n${decodeEntities(t.replace(/<[^>]+>/g, ''))}\n\`\`\`\n\n`);
  h = h.replace(/<p[^>]*>([\s\S]*?)<\/p>/gi, (_, t) => `\n\n${inline(t)}\n\n`);
  h = h.replace(/<\/(div|section|header|ul|ol|tr|table)>/gi, '\n\n');
  // whatever survives: strip remaining tags, decode, tidy
  h = inline(h);
  h = h.replace(/\n{3,}/g, '\n\n').replace(/[ \t]+\n/g, '\n').trim();
  return h;
}

// inline-level cleanup: links/strong/em/code kept as markdown, other tags dropped
function inline(t) {
  return decodeEntities(
    t
      .replace(/<a\b[^>]*href="([^"]*)"[^>]*>([\s\S]*?)<\/a>/gi, (_, href, txt) => {
        const label = txt.replace(/<[^>]+>/g, '').trim();
        return href && label ? `[${label}](${href})` : label;
      })
      .replace(/<(strong|b)\b[^>]*>([\s\S]*?)<\/\1>/gi, (_, __, x) => `**${x.replace(/<[^>]+>/g, '')}**`)
      .replace(/<(em|i)\b[^>]*>([\s\S]*?)<\/\1>/gi, (_, __, x) => `*${x.replace(/<[^>]+>/g, '')}*`)
      .replace(/<code\b[^>]*>([\s\S]*?)<\/code>/gi, (_, x) => `\`${decodeEntities(x.replace(/<[^>]+>/g, ''))}\``)
      .replace(/<br\s*\/?>/gi, '\n')
      .replace(/<[^>]+>/g, '')
  ).replace(/[ \t]{2,}/g, ' ').trim();
}

function meta(html) {
  const title = (html.match(/<title>([\s\S]*?)<\/title>/i)?.[1] || '').trim();
  const desc = (html.match(/<meta\s+name="description"\s+content="([^"]*)"/i)?.[1] || '').trim();
  return { title: decodeEntities(title), desc: decodeEntities(desc) };
}

// ---- walk dist ----------------------------------------------------------------

async function* htmlFiles(dir) {
  for (const e of await readdir(dir, { withFileTypes: true })) {
    const p = join(dir, e.name);
    if (e.isDirectory()) yield* htmlFiles(p);
    else if (e.name.endsWith('.html')) yield p;
  }
}

function urlPathFor(file) {
  let rel = relative(DIST, file).replace(/\\/g, '/');
  if (rel.endsWith('/index.html')) rel = rel.slice(0, -'index.html'.length);
  else rel = rel.replace(/\.html$/, '/');
  return '/' + rel.replace(/\/$/, '') || '/';
}

async function run() {
  try { await stat(DIST); } catch { console.error('gen-llms: dist/ not found — run astro build first'); process.exit(1); }
  const pages = [];
  for await (const file of htmlFiles(DIST)) {
    const raw = await readFile(file, 'utf8');
    const { title, desc } = meta(raw);
    const md = stripToMarkdown(raw);
    // write the .md twin next to the html path
    let rel = relative(DIST, file).replace(/\\/g, '/');
    const mdRel = rel === 'index.html' ? 'index.md' : rel.replace(/\/index\.html$/, '.md').replace(/\.html$/, '.md');
    const outPath = join(DIST, mdRel);
    const url = (rel.endsWith('/index.html') || rel === 'index.html')
      ? '/' + rel.replace(/index\.html$/, '')
      : '/' + rel.replace(/\.html$/, '');
    const header = `# ${title || url}\n\n> ${desc}\n> Source: ${SITE}${url}\n\n---\n\n`;
    await writeFile(outPath, header + md + '\n', 'utf8');
    pages.push({ url: url.replace(/\/$/, '') || '/', mdUrl: '/' + mdRel, title, desc, md });
  }

  // stable order: root first, then alphabetical
  pages.sort((a, b) => (a.url === '/' ? -1 : b.url === '/' ? 1 : a.url.localeCompare(b.url)));

  // llms.txt — the curated index
  const idx = [
    `# QIQT-H — One Wave Function, One World`,
    ``,
    `> A single-world (Φ,λ) formulation of quantum theory with an AdS/CFT-style holographic`,
    `> duality for flat spacetime, derived from five postulates and machine-verified in Lean 4.`,
    `> This file indexes LLM-readable Markdown twins of every page (append .md to any URL).`,
    ``,
    `## Pages`,
    ...pages.map(p => `- [${p.title || p.url}](${SITE}${p.mdUrl})${p.desc ? ': ' + p.desc : ''}`),
    ``,
  ].join('\n');
  await writeFile(join(DIST, 'llms.txt'), idx, 'utf8');

  // llms-full.txt — everything concatenated
  const full = pages.map(p =>
    `${'='.repeat(80)}\n# ${p.title || p.url}\nURL: ${SITE}${p.url}\n${'='.repeat(80)}\n\n${p.md}\n`
  ).join('\n\n');
  await writeFile(join(DIST, 'llms-full.txt'), full, 'utf8');

  console.log(`gen-llms: wrote ${pages.length} .md twins + llms.txt + llms-full.txt`);
}

run();
