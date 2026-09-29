# Maintaining recorded views

A figure is actual reader output recorded for its adjacent Lean source. Its HTML/SVG remains static: controls inside it do not run. Captions distinguish full views, excerpts and saved-history output. Preserve those distinctions when replacing a recording.

## Public build manifest

`source-assets/views/views.json` version 2 contains recording time, Lean version, display settings, reviewed captions and SHA-256 pins for every fragment, source, stylesheet and screenshot. It deliberately omits capture receipts and development revision metadata. Pins establish file integrity, not scientific correctness or proof.

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
