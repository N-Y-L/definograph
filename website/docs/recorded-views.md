# Maintaining recorded views

A figure is actual reader output recorded for its adjacent Lean source. Its HTML/SVG remains static: controls inside it do not run. Captions distinguish full views, excerpts and saved-history output. Preserve those distinctions when replacing a recording.

## Public build manifest

`source-assets/views/views.json` version 2 contains recording or rendering time, the input’s Lean version, display settings, reviewed captions and SHA-256 pins for every fragment, source, stylesheet and screenshot. It deliberately omits capture receipts and development revision metadata. Pins establish file integrity, not scientific correctness or proof.

A batch rendered again without rerunning Lean adds `renderedFromSavedData: true` and records its actual renderer theme as `recordedTheme: "light"` or `"dark"`. Its `createdAt` is the new rendering/export timestamp, not the native-capture time. Every view in that batch must include `nativeCapture`: either `null` when the native date is unavailable, or exactly `{ "startedAt": "…", "completedAt": "…" }` with verified ISO 8601 timestamps. Use identical timestamps when only a single capture timestamp is evidenced. The interval must be ordered and must not end after the rendering. Do not infer a native date from an older batch’s `createdAt`. Public provenance displays the native date or date range in UTC; the manifest retains the exact interval.

An HTML batch whose original renderer styles support both website themes may also set `adaptiveTheme: true`; this marker is either true or absent and requires `recordedTheme`. Set it only after the export pipeline verifies the unchanged fragment and renderer styles in both modes. It changes no capture provenance and makes no claim of a fresh Lean run. HTML figures then say “Adapts to page theme”; fixed HTML figures and screenshots name their recorded light or dark theme. PNG screenshots always remain fixed, even when their batch has adaptive HTML.

The importer reads the batch markers and theme from `manifest.json`, and `nativeCapture` from each view’s `meta.recordedState.nativeCapture`. It copies only these public fields, never private capture paths or hashes. Keep `savedRecord: true` only for saved editor inspection histories; ordinary saved native results do not become histories. All new saved-data views require an explicit native value, including `null`, and unexpected native-capture fields are rejected. Older batches need no migration and retain their original labels and canvas markup. An explicit `recordedTheme` is also permitted on other batches; it describes the recorded renderer, never the website visitor’s preference.

A new rendering keeps the original source bytes and saved outcomes unchanged. Give it a new batch ID and pins for the genuinely regenerated output. Review captions again when the provenance or theme behavior changes, even if the pixels happen to match. A changed rendering date alone does not require another caption review. In particular, a screenshot of an editor panel rendered from saved data outside Visual Studio Code must not be described as a fresh editor action. The figure label states that Lean was not rerun; it does not promote saved results to current checking evidence.

The build validates every named asset. A changed file requires an intentional pin update and review. It checks that fragments are inert, self-contained and free of local paths or hidden run identifiers. Any explicitly permitted short identifier must appear as visible recorded text, never an attribute. Screenshots have pinned dimensions and no metadata chunks.

Each batch stylesheet is restricted to its recorded views and cannot load external resources. The build confines it further to that batch, strips comments, renames used animation keyframes and drops unused ones. It checks that every fragment reference resolves and every animation has a defined, scoped name.

## Import a recording

```sh
npm run import-views -- /path/to/public-candidates/batch-name --dry-run
npm run import-views -- /path/to/public-candidates/batch-name
npm run check
```

A capture package contains `manifest.json`, `views.css` and a directory per view containing `fragment.html`, `source.lean`, `meta.json` and optionally `context@2x.png`. The source package must have a matching `READY-*.json` declaration in its parent or grandparent. Its status must be `ready` or `complete`, and it must pin the manifest hash. If several declarations name that manifest, the most recent determines acceptance. Missing, unfinished or mismatched declarations are refused.

The importer verifies the package before copying publishable files. It never copies `meta.json`. With a version-2 destination it removes CSS comments, pins the resulting stylesheet and retains only public batch fields. The receipt returned by the import reports its private acceptance evidence; retain that separately if needed. Legacy version-1 destinations retain the earlier private provenance format and should not be published as source.

Use `--replaces batch-name` to replace a complete batch, or `--replaces-view view-id` for a capture-only entry. These options remove the replaced source assets, so review the dry run and retain the existing source before applying them. Never edit the recorded diagram to invent a different reader result.

New or changed captions are marked as drafts until reviewed. Check the exact source pairing, view coverage, caption, alt text, excerpt label and saved-history label before clearing the draft flag. Imported screenshots may contain a full window or a disclosed excerpt; show them at their intended size with a full-size link.

## Presentation and verification

Figures retain the reader's colors and shapes. A transparent recording root lets the surrounding canvas reproduce its original white card, cream panel or page background. Wide diagrams scroll inside a keyboard-focusable region; supported reflowing views wrap instead. Long sources and long panels can use labelled disclosures. Print styles show the material without scrollbars, shrinking wide views where necessary.

After an update, run `npm run check` and inspect affected figures in a browser at narrow and wide sizes, with keyboard navigation and print output when relevant. Compare the figure to its source recording. Confirm readable labels, focus visibility, source disclosure behavior and the caption's factual limits. A passing integrity check cannot establish that a diagram's interpretation is correct.

## Static mathematical labels

A batch that contains generated KaTeX labels may additionally declare `mathAssets`:

```json
{
  "engine": "katex",
  "version": "0.18.7",
  "fonts": [{ "file": "assets/fonts/KaTeX_AMS-Regular.woff2", "sha256": "…", "bytes": 28076, "mime": "font/woff2" }],
  "license": { "file": "assets/licenses/KaTeX-LICENSE.txt", "sha256": "…", "bytes": 1107, "mime": "text/plain" },
  "stylesheet": { "file": "math-fonts.css", "sha256": "…", "bytes": 3291, "mime": "text/css" }
}
```

The abbreviated example shows the shape; all 20 WOFF2 faces, in the order and with the exact pins in `scripts/katex-fonts-approved.json`, are required. The importer rejects missing or extra fields, other versions, changed bytes, noncanonical font CSS, and symlinked font inputs. The license is the unmodified package MIT license. The separate `math-fonts.css` contains only the canonical approved faces, with their original families, styles, weights and `font-display:block`. `views.css` remains resource-free: its existing `url()`, `@import` and `@font-face` bans are unchanged.

The build verifies this package before generating its own same-origin font URLs. Only batches used as HTML figures contribute fonts; screenshots do not. Identical packages are emitted once under `/assets/math/katex-0.18.7/`, with the license alongside them. The font files have MIME type `font/woff2`; CSP permits same-origin fonts while continuing to forbid scripts. Neither KaTeX JavaScript nor an online math service is shipped. Old batches without `mathAssets` keep their original markup and introduce no fonts.

The `foreignObject` exception is limited to the reader's measured `MathLabel` structure: an SVG group carrying its original source label and title, one XHTML host, and one KaTeX label with both accessible MathML and visually rendered HTML. The hidden MathML is retained; the visual copy remains `aria-hidden`. Explicit tag, attribute and namespace checks still reject arbitrary HTML, links, resources, active elements, events and inline styles. Extracted CSS classes preserve the renderer's styles. Source/title/accessible-label agreement and the source-plus-TeX measurement key are checked, but that cache key is not a checked Lean identifier. Nested TeX braces are permitted only in validated math annotation/key contexts; site directives remain prohibited.

The same strict KaTeX subtree rules also cover inline mathematical labels in the reader’s restricted-map law cards. Their original source labels and measured font sizes remain attached to each label; this does not permit arbitrary inline HTML.

These are static HTML figures containing SVG and HTML, not portable standalone SVG files. Batches with measured mathematical labels bypass the site’s optional CSS zoom: zoom can change HTML font metrics relative to the captured SVG baseline. Their measured minimum widths and local scroll frames still protect label size. The importer requires a positive measured minimum for these batches and retains it even when the layout can reflow above that width; an existing site-specific minimum can increase this floor, never lower it. Acceptance of a new renderer still requires browser measurements after local fonts finish loading: visible `.katex-html` glyph bounds and scale, foreignObject/HTML overflow, source associations, light and dark modes, narrow layouts and print. An SVG `<text>` size check alone does not cover HTML math labels. Asset pins and these format checks establish integrity and safe rendering, not mathematical equivalence or a new Lean check.

`node scripts/math-selftest.mjs` exercises source-derived notation fixtures and deliberately malicious variants. The fixtures are test inputs, not published reader recordings.
