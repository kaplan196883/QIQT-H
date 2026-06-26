import { defineConfig } from 'astro/config';
import remarkMath from 'remark-math';
import rehypeKatex from 'rehype-katex';

// Custom domain (CNAME = qiqt.org) → served from the site root, so no `base`.
export default defineConfig({
  site: 'https://qiqt.org',
  markdown: {
    remarkPlugins: [remarkMath],
    // allow \href, but only to internal anchors / same-site paths (no external/JS URLs),
    // so identifiers inside formulas can link to their definitions on the browser page.
    rehypePlugins: [[rehypeKatex, {
      trust: (ctx) => ctx.command === '\\href' && /^(#|\/)/.test(ctx.url),
      strict: false,
    }]],
    shikiConfig: { theme: 'github-dark' },
  },
});
