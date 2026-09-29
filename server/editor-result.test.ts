import { test } from 'node:test';
import assert from 'node:assert/strict';
import { parseEditorResult } from './editor-result.js';

test('exact attachment retains bytes independently of legacy number and nesting policy', () => {
  const deep = '['.repeat(160) + '0' + ']'.repeat(160);
  const result = parseEditorResult(`{"ok":true,"diagnostics":[],"legacy":{"estimate":0.125,"deep":${deep}},"sourceSnapshot":{"source":"quoted \\\" },[, sourceSnapshot ","natural":["nat","9007199254740993"]}}`);
  assert.equal((result.legacy as { estimate: number }).estimate, 0.125);
  assert.deepEqual((result.sourceSnapshot as { natural: string[] }).natural, ['nat', '9007199254740993']);
});
test('duplicate response or nested attachment fields and rounded integers are rejected', () => {
  for (const text of [
    '{"ok":true,"ok":false,"diagnostics":[]}',
    '{"ok":true,"diagnostics":[],"sourceSnapshot":{"x":1,"x":2}}',
    '{"ok":true,"diagnostics":[],"sourceSnapshot":{"x":9007199254740993}}',
    '{"ok":true,"diagnostics":[],"sourceSnapshot":{},"sourceSnapshot":{}}',
    '{"ok":true,"diagnostics":[],"sourceOccurrence":{"path":[],"path":["appArg"]}}',
    '{"ok":true,"diagnostics":[],"sourceOccurrence":{"number":9007199254740993}}',
    '{"ok":true,"diagnostics":[],"sourceOccurrence":{},"sourceOccurrence":{}}',
    '{"ok":true,"diagnostics":[],"sourceHeadExposure":{"target":"term","target":"type"}}',
    '{"ok":true,"diagnostics":[],"sourceHeadExposure":{"number":9007199254740993}}',
    '{"ok":true,"diagnostics":[],"sourceHeadExposure":{},"sourceHeadExposure":{}}',
    '{"ok":true,"diagnostics":[],"sourceDecomposition":{"steps":[],"steps":[{}]}}',
    '{"ok":true,"diagnostics":[],"sourceDecomposition":{"receiptStart":9007199254740993}}',
    '{"ok":true,"diagnostics":[],"sourceDecomposition":{},"sourceDecomposition":{}}',
  ]) assert.throws(() => parseEditorResult(text), /duplicate|Duplicate|safe browser/);
});
