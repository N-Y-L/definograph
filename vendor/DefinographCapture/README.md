# Definograph source capture dependency

This is the exact `SourceCapture` import closure from source commit
`747631072c57c118a409d4e16280d29a33e05a20` of the separately maintained
Definograph foundation. That source repository remains authoritative.
`UPSTREAM.json` records its `deps.json` identity, original source paths,
SHA-256 hashes, direct imports, and dependency order. The 26 files retain their
original module names and bytes. Fixture and packet-worker modules are excluded.

The library targets Lean 4.28.0 and imports only its bundled core libraries
outside this closure. The native build verifies the snapshot, stages it into a
fresh isolated build directory, and generates `.olean` and C outputs. Those C
outputs are linked into the editor context sidecar; the standalone worker and
the formal project's runtime import paths do not acquire this dependency.

To refresh, select a reviewed upstream commit and read its pinned `deps.json`.
Verify every source against that inventory, compute the transitive import closure
rooted at `SourceCapture`, and copy the exact bytes in upstream dependency order.
Update the source commit and manifest together, including the expected commit
in `scripts/source-capture-dependency.mjs`. Do not edit the copied sources or
reuse compiled artifacts from an older snapshot. Run the portable dependency
tests, rebuild the native context sidecar, and run its source/editor integration
checks before using the refreshed build. Local configuration records the source
package digest and compiled artifact fingerprint.

From the application root, run the portable checks without Lean or downloads:

```sh
node --test scripts/source-capture-dependency.test.mjs
```

No upstream license file was present at this commit. No license is added to
this snapshot.
