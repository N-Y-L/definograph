import { defineConfig } from 'vite';
export default defineConfig({
  // Relative assets serve both localhost and the VS Code webview resource origin.
  base: './',
  server: {
    host: '127.0.0.1', port: 5173, strictPort: true,
    watch: { ignored: ['**/.local/**', '**/.lake/**'] },
    proxy: { '/api': { target: 'http://127.0.0.1:4317', changeOrigin: true } },
  },
  build: { target: 'es2022' },
});
