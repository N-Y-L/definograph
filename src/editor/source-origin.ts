/** A host-side association with one completed process, not a portable certificate
 * or a digest of every imported declaration. Saved copies do not restore trust. */
export interface SourceSnapshotOrigin {
  kind: 'local-editor-process-snapshot';
  captureId: string;
  sourceSha256: string;
  engine: { contextSha256: string; buildFingerprint: string; packageSha256: string; leanSha256: string };
  project: { root: string; toolchain: string; libraryPaths: string[]; dependencyTracking: 'snapshot-paths-only' };
  document: { uri: string; version: number } | null;
  selection: { start: { line: number; character: number }; end: { line: number; character: number } };
  policyId: 'named-source-v1';
}

const record = (v: unknown): v is Record<string, unknown> => !!v && typeof v === 'object' && !Array.isArray(v);
const digest = (v: unknown) => typeof v === 'string' && /^[a-f0-9]{64}$/.test(v);
const coordinate = (v: unknown) => record(v) && Number.isSafeInteger(v.line) && Number(v.line) >= 0 && Number.isSafeInteger(v.character) && Number(v.character) >= 0;
export function isSourceSnapshotOrigin(v: unknown): v is SourceSnapshotOrigin {
  return record(v) && v.kind === 'local-editor-process-snapshot' && typeof v.captureId === 'string'
    && /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/.test(v.captureId)
    && digest(v.sourceSha256) && record(v.engine) && ['contextSha256', 'buildFingerprint', 'packageSha256', 'leanSha256'].every(k => digest((v.engine as Record<string, unknown>)[k]))
    && record(v.project) && typeof v.project.root === 'string' && typeof v.project.toolchain === 'string'
    && v.project.dependencyTracking === 'snapshot-paths-only' && Array.isArray(v.project.libraryPaths)
    && v.project.libraryPaths.length <= 64 && v.project.libraryPaths.every(p => typeof p === 'string')
    && (v.document === null || record(v.document) && typeof v.document.uri === 'string' && Number.isSafeInteger(v.document.version) && Number(v.document.version) >= 0)
    && record(v.selection) && coordinate(v.selection.start) && coordinate(v.selection.end) && v.policyId === 'named-source-v1';
}
