import { defineConfig } from 'vitest/config';
// Several renderer tests take seconds on a slow shared runner, and the default limit of five
// seconds has failed the public build on timing alone. Twenty seconds leaves room for a slow
// runner and still stops a test that hangs.
export default defineConfig({ test: { include: ['src/**/*.test.ts'], environment: 'node', testTimeout: 20_000 } });
