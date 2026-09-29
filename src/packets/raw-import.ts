/** Local source data carries exact identity, but no semantic or kernel claim. */
import { createExactJsonTools, type JsonValue } from './packet';
import { buildRawInspection, readRawInspection, type RawError, type RawInspectionDrawing } from './raw';

export interface ImportedRawSource {
  readonly identity: string;
  readonly sourceText: string;
  readonly value: JsonValue;
  readonly drawing: RawInspectionDrawing;
}

export class RawImportError extends Error {
  readonly code: RawError['code'];
  readonly path: RawError['path'];
  constructor(error: RawError) {
    super(error.message);
    this.name = 'RawImportError'; this.code = error.code; this.path = [...error.path];
  }
}

/** Share the packet JSON/byte boundary without accepting packet trust claims.
 * Identity is SHA-256 of canonical JSON; original text remains independently
 * available, including whitespace and the original object-key order. */
export async function parseRawSourceText(sourceText: string): Promise<ImportedRawSource> {
  const { parse, canonical, hash, freeze } = createExactJsonTools();
  const value = parse(sourceText);
  const identity = await hash(value);
  const built = buildRawInspection({ family: 'frame', value }, { sourceIdentity: identity, sourcePath: [] });
  if (!built.ok) throw new RawImportError(built.error);
  const readback = readRawInspection(built.value);
  if (!readback.ok) throw new RawImportError(readback.error);
  if (readback.value.family !== 'frame' || canonical(readback.value.value) !== canonical(value)) {
    throw new RawImportError({ code: 'malformed', message: 'raw drawing readback differs from the imported frame', path: [] });
  }
  const imported = { identity, sourceText, value, drawing: built.value };
  freeze(imported);
  return imported;
}
