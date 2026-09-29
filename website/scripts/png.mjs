// Reads the structure of a PNG file without decoding its pixels: the signature, the
// chunk sequence and CRCs, the IHDR dimensions, and any textual or metadata chunks.
// Published images are copied byte for byte, so this only inspects; it never rewrites.
import { crc32, inflateSync } from 'node:zlib';

const SIGNATURE = Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]);
const METADATA_CHUNKS = new Set(['tEXt', 'zTXt', 'iTXt', 'eXIf', 'tIME']);

function textChunk(type, data, errors) {
  const nul = data.indexOf(0);
  if (nul < 1) {
    errors.push(`${type} chunk has no keyword`);
    return null;
  }
  const keyword = data.toString('latin1', 0, nul);
  try {
    if (type === 'tEXt') return { type, keyword, value: data.toString('latin1', nul + 1) };
    if (type === 'zTXt') return { type, keyword, value: inflateSync(data.subarray(nul + 2)).toString('latin1') };
    // iTXt: keyword, compression flag and method, language tag, translated keyword, text.
    const compressed = data[nul + 1] === 1;
    const language = data.indexOf(0, nul + 3);
    const translated = data.indexOf(0, language + 1);
    const text = data.subarray(translated + 1);
    return { type, keyword, value: (compressed ? inflateSync(text) : text).toString('utf8') };
  } catch {
    errors.push(`${type} chunk "${keyword}" cannot be read`);
    return null;
  }
}

// Returns { errors, width, height, chunks, text, metadata, animated }.
export function readPng(bytes) {
  const errors = [];
  if (bytes.length < SIGNATURE.length || !bytes.subarray(0, SIGNATURE.length).equals(SIGNATURE)) {
    return { errors: ['not a PNG file (bad signature)'], width: 0, height: 0, chunks: [], text: [], metadata: [], animated: false };
  }
  const chunks = [];
  let offset = SIGNATURE.length;
  while (offset + 12 <= bytes.length) {
    const length = bytes.readUInt32BE(offset);
    const type = bytes.toString('latin1', offset + 4, offset + 8);
    const end = offset + 12 + length;
    if (end > bytes.length) {
      errors.push(`chunk ${type} runs past the end of the file`);
      break;
    }
    if (crc32(bytes.subarray(offset + 4, offset + 8 + length)) !== bytes.readUInt32BE(offset + 8 + length)) {
      errors.push(`chunk ${type} has a bad CRC`);
    }
    chunks.push({ type, data: bytes.subarray(offset + 8, offset + 8 + length) });
    offset = end;
    if (type === 'IEND') break;
  }
  if (chunks[0]?.type !== 'IHDR' || chunks[0].data.length !== 13) errors.push('the first chunk is not a valid IHDR');
  if (chunks.at(-1)?.type !== 'IEND') errors.push('the file does not end with IEND');
  else if (offset !== bytes.length) errors.push(`${bytes.length - offset} bytes follow the IEND chunk`);
  if (!chunks.some((chunk) => chunk.type === 'IDAT')) errors.push('the file has no image data');

  const ihdr = chunks[0]?.type === 'IHDR' && chunks[0].data.length === 13 ? chunks[0].data : null;
  const text = chunks.filter((chunk) => ['tEXt', 'zTXt', 'iTXt'].includes(chunk.type)).map((chunk) => textChunk(chunk.type, chunk.data, errors)).filter(Boolean);
  return {
    errors,
    width: ihdr ? ihdr.readUInt32BE(0) : 0,
    height: ihdr ? ihdr.readUInt32BE(4) : 0,
    chunks: chunks.map((chunk) => chunk.type),
    text,
    metadata: chunks.filter((chunk) => METADATA_CHUNKS.has(chunk.type)).map((chunk) => ({ type: chunk.type, data: chunk.data })),
    animated: chunks.some((chunk) => chunk.type === 'acTL'),
  };
}
