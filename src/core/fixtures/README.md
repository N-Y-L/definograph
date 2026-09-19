These JSON trees are actual output from the pinned Lean 4.28.0 extractor, not handwritten approximations. Each includes its input source and Lean version. They exercise Lean's implicit argument order, canonical instance metadata, zero-vector numerals, lambda binder identity, and rejection of custom instances in the portable TypeScript core.

The live extractor is exercised separately by the Lean integration checks. These snapshots allow the renderer's semantic tests to run without downloading Lean or mathlib.
