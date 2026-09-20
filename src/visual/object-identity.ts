/** Stable visual identity shared by construction, clause, and sequence views. */
const palette = ['#387b79', '#596a9d', '#77648c', '#947149', '#3f748c', '#886b60', '#63784f', '#6c7594'];
export function readingObjectColor(id: string): string {
  let hash = 0;
  for (let index = 0; index < id.length; index++) hash = (Math.imul(hash, 31) + id.charCodeAt(index)) | 0;
  return palette[(hash >>> 0) % palette.length];
}
