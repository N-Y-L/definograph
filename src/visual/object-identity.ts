/** Stable visual identity shared by construction, clause, and sequence views. */
const palette = ['#387b79', '#536497', '#725f87', '#836139', '#3f748c', '#83665b', '#63784f', '#656e8d'];
export function readingObjectColor(id: string): string {
  let hash = 0;
  for (let index = 0; index < id.length; index++) hash = (Math.imul(hash, 31) + id.charCodeAt(index)) | 0;
  return palette[(hash >>> 0) % palette.length];
}
