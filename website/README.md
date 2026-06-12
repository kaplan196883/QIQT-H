# qiqt.org

The website for the **QIQT-H** research program (*Quantized Information Quantum Theory — Holographic*).
Built with [Astro](https://astro.build): static output, Markdown content with KaTeX math, zero client-side
JS beyond the math renderer. Deploys to GitHub Pages on every push to `main`.

## Develop

```bash
cd website
npm install
npm run dev        # http://localhost:4321
```

## Build

```bash
npm run build      # static site → website/dist
npm run preview    # serve the production build locally
```

## Structure

```
website/
  astro.config.mjs          # site URL + remark-math / rehype-katex
  public/
    CNAME                    # qiqt.org (custom domain)
    .nojekyll                # tell Pages not to run Jekyll
  src/
    styles/global.css        # the Hybrid design system
    layouts/
      Base.astro             # landing register (homepage)
      Deep.astro             # austere prose register (Markdown pages)
    components/
      Nav.astro  Footer.astro  Chain.astro  StatusTable.astro
    pages/
      index.astro            # homepage
      idea.md  theory.md  formalization.md
      open-problems.md  papers.md  about.md
```

Prose pages are Markdown with a `layout: ../layouts/Deep.astro` frontmatter and `title` / `eyebrow` /
`description` fields. Inline math is `$...$`, display math `$$...$$`, rendered to HTML at build time by
rehype-katex (no runtime KaTeX on those pages). The homepage and its components use client-side
`renderMathInElement` for the few `\( ... \)` spans in `.astro` markup.

## Deploy (GitHub Pages)

Deployment is automated by `.github/workflows/deploy.yml` **at the repository root** (Actions only reads
workflows from the root `.github/workflows/`, not from `website/`). On push to `main` touching `website/**`
it builds and publishes `website/dist`.

One-time setup in the GitHub repo:

1. **Settings → Pages → Build and deployment → Source: GitHub Actions.**
2. **Settings → Pages → Custom domain:** enter `qiqt.org` (the `public/CNAME` file already carries it into
   the build output). Enable *Enforce HTTPS* once the certificate is issued.
3. At your DNS provider, point `qiqt.org` at GitHub Pages:
   - apex `A` records → `185.199.108.153`, `185.199.109.153`, `185.199.110.153`, `185.199.111.153`
   - and/or `AAAA` records → `2606:50c0:8000::153` … `:8003::153`
   - `www` `CNAME` → `kaplan196883.github.io`

The repository must be public (or on a plan that allows Pages on private repos). After the first successful
Action run, the site is live at `https://qiqt.org`.
