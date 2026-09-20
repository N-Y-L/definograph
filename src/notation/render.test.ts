import { describe, expect, it } from 'vitest';
import { typesetStatement } from './render';
describe('bounded local mathematical typesetting',()=>{
  it('renders quantifier order with accessible math and no remote dependency',()=>{
    const result=typesetStatement('\\forall x \\in \\mathbb{R},\\ \\exists y,\\ x < y');
    expect(result.status).toBe('rendered');
    if(result.status==='rendered') {expect(result.html).toContain('<math');expect(result.html).toContain('∀');expect(result.html).toContain('∃');expect(result.html).not.toContain('<script');}
  });
  it('does not enable links, images, or arbitrary HTML from TeX',()=>{
    for(const latex of ['\\href{https://example.com}{x}','\\includegraphics{https://example.com/x.png}','\\htmlStyle{position:fixed}{x}']) {
      const result=typesetStatement(latex);
      if(result.status==='rendered'){expect(result.html).not.toMatch(/<(?:a|img|script)\b/);expect(result.html).not.toContain('position:fixed');}
    }
  });
  it('falls back on unsupported notation and expansion loops',()=>{
    expect(typesetStatement('\\notARealCommand{x}').status).toBe('unavailable');
    expect(typesetStatement('\\def\\recurse{\\recurse}\\recurse').status).toBe('unavailable');
    expect(typesetStatement('x'.repeat(65537)).status).toBe('unavailable');
  });
  it('does not leak macro state between statements',()=>{
    expect(typesetStatement('\\gdef\\statementlensmacro{x}\\statementlensmacro').status).toBe('rendered');
    expect(typesetStatement('\\statementlensmacro').status).toBe('unavailable');
  });
});
