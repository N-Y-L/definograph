import { defineConfig } from 'vite';
export default defineConfig({
  // Relative assets serve both localhost and the VS Code webview resource origin.
  base: './',
  server: {
    host: '127.0.0.1', port: 5173, strictPort: true,
    watch: { ignored: ['**/.local/**', '**/.lake/**'] },
    proxy: { '/api': { target: 'http://127.0.0.1:4317', changeOrigin: true } },
  },
  // Never inline assets as data: URLs. Neither the local server's CSP (font-src 'self') nor the editor
  // webview's (font-src <webview source>) allows data: fonts, so an inlined KaTeX font would be blocked.
  build: { target: 'es2022', assetsInlineLimit: 0 },
});
