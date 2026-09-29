# Definograph website

The tutorial, examples and reference at [definograph.com](https://definograph.com). The site builds to static HTML and CSS. Its diagrams are recorded output from the real reader, with the exact Lean source beside each figure. It runs no Lean and ships no JavaScript to the browser.

For the reader itself, use the [project README](https://github.com/N-Y-L/definograph#readme).

## Quick start

Use Node.js 22.12 or later. From this directory:

```sh
npm ci --ignore-scripts
npm run check
npm run dev
```

Open <http://127.0.0.1:4173>. The server rebuilds after content, template or asset edits; restart it after editing build scripts. `npm run build` writes `dist/`. `npm run preview` serves an existing build.

`npm run check` rebuilds and verifies routes, links, source listings, asset hashes, recorded-view safety, response headers and local HTTP behavior. It also tests malformed imports. Browser layout and the deployed host need separate verification.

## Edit the site

| Path | Purpose |
| --- | --- |
| `content/` | Home, Examples, Reference, Setup and 404 page fragments |
| `tutorial/` | Seven lessons, exercises and downloadable Lean examples |
| `templates/page.html` | Shared navigation, document and footer |
| `source-assets/site.css` | Site layout and typography |
| `source-assets/views/` | Recorded HTML/SVG, screenshots, Lean sources and pinned public manifest |
| `scripts/site.mjs` | Routes, allowed outputs and teaching-source digests |
| `scripts/` | Build, checks, imports and local server |

Use root-relative page links with trailing slashes. `{{view:id}}` inserts a recorded figure, its label, source and caption; `{{capture:id}}` inserts an application screenshot. In Markdown, put each directive in its own paragraph. `{{source:Example.lean}}` inserts a published Lean example. Update its digest deliberately when changing the source.

See [recorded-view maintenance](docs/recorded-views.md) for the import format, review requirements and rendering safeguards. Synthetic test fixtures in `scripts/fixtures/` are not reader output and never enter `dist/`.

## Publish

Deploy **only `dist/`**, including `_headers` and `_redirects`. `wrangler.jsonc` describes the existing Cloudflare Worker and static-asset routing. Use a frozen, checked build; verify the live pages, downloads, redirects and custom 404 after deployment. Retain the previous deployment for rollback.

The source manifest records public asset integrity and recording dates. Private capture receipts, raw metadata, credentials, local paths and Git history are not part of a website source export. The website does not provide a qualified installer or Marketplace release.
