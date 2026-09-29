# Test fixture: not Definograph output

A hand-written batch in the recorded-view package format, used only by the checks to
exercise the import, validation and figure code. The build never reads this directory
and nothing here is published. Do not present it as reader output.

`../READY-fixture.json` declares this batch's `manifest.json` by its SHA-256, as a pipeline's
READY file does; the import refuses a batch that no READY file beside it declares. Update
that hash whenever `manifest.json` changes.
