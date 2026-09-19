import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import { examples } from '../src/examples.ts';
import { ballGeometry, collectBinders, discoverScenes, evaluateExpression, initialScenario, sampleGraph, sliceGeometry, updateScenario } from '../src/core/index.ts';
import type { Analysis } from '../src/core/types.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
const analyses = new Map<string, Analysis>();
let checks = 0;
try {
  for (const example of examples) {
    const result = await backend.analyze(example.source);
    assert.equal(result.ok, true, `${example.id}: ${result.error ?? 'elaboration failed'}`);
    const analysis = result as unknown as Analysis;
    analyses.set(example.id, analysis);
    const scenes = discoverScenes(analysis.tree);
    const scenario = initialScenario(analysis.tree);
    assert.ok(scenes.length > 0, `${example.id}: no visualizable fragment discovered`);
    for (const scene of scenes) {
      if (scene.kind === 'ball') {
        const geometry = ballGeometry(scene, scenario);
        assert.equal(geometry.status, 'geometry', `${example.id}: ball failed numerical interpretation`);
        if (scene.dimension >= 2) assert.equal(sliceGeometry(scene, scenario).status, 'geometry', `${example.id}: slice failed`);
      }
      if (scene.kind === 'graph') {
        const samples = sampleGraph(scene, scenario, { count: 9 });
        assert.equal(samples.length, 9);
        assert.ok(samples.every(sample => sample.y !== null), `${example.id}: graph has unavailable samples`);
      }
      if (scene.kind === 'interval') {
        assert.equal(evaluateExpression(scene.left, scenario).status, 'value', `${example.id}: left condition operand unavailable`);
        assert.equal(evaluateExpression(scene.right, scenario).status, 'value', `${example.id}: right condition operand unavailable`);
      }
    }
    console.log(`PASS ${example.id}: Lean → typed tree → ${scenes.map(scene => scene.kind).join(', ')}`);
    checks += 1;
  }
  const product = analyses.get('product')!;
  const productScene = discoverScenes(product.tree).find(scene => scene.kind === 'ball');
  assert.equal(productScene?.kind === 'ball' ? productScene.metric : undefined, 'sup2');

  const sphere = analyses.get('sphere')!;
  const sphereScene = discoverScenes(sphere.tree).find(scene => scene.kind === 'ball');
  assert.ok(sphereScene?.kind === 'ball');
  const slice = sliceGeometry(sphereScene, initialScenario(sphere.tree), { fixed: [0, 0, 1, 0] });
  assert.equal(slice.status, 'geometry');
  if (slice.status === 'geometry') {
    assert.equal(slice.ambientDimension, 4);
    assert.equal(slice.intrinsicDimension, 3);
    assert.ok(Math.abs(slice.radius - Math.sqrt(3)) < 1e-12);
  }
  const fn = analyses.get('function')!;
  const fnScenes = discoverScenes(fn.tree);
  assert.ok(fnScenes.some(scene => scene.kind === 'mapping'));
  const graph = fnScenes.find(scene => scene.kind === 'graph');
  assert.ok(graph?.kind === 'graph');
  assert.deepEqual(sampleGraph(graph, initialScenario(fn.tree), { min: -1, max: 1, count: 3 }), [{ x: -1, y: -1 }, { x: 0, y: 1 }, { x: 1, y: 3 }]);

  const depends = analyses.get('depends')!;
  const [x, y] = collectBinders(depends.tree);
  assert.ok(x && y);
  const changed = updateScenario(depends.tree, { [x.id]: 0, [y.id]: 5 }, x.id, 2);
  assert.equal(changed[y.id], undefined, 'Dependent existential must require a fresh candidate');
  const fixed = analyses.get('fixed')!;
  const [fixedY, laterX] = collectBinders(fixed.tree);
  assert.ok(fixedY && laterX);
  assert.equal(updateScenario(fixed.tree, { [fixedY.id]: 5, [laterX.id]: 0 }, laterX.id, 2)[fixedY.id], 5);
  console.log('PASS actual metrics, high-dimensional slice, function graph/mapping, and witness dependency behavior');
  checks += 1;
  console.log(`${checks}/${examples.length + 1} native Lean-to-visualizer integration checks passed.`);
} finally {
  backend.close?.();
}
