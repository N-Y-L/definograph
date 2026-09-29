// Reads the subset of the `_headers` format this site uses: comment lines, path
// patterns (exact paths or a single `*` splat) and indented `Name: value` lines.
// Anything else is rejected rather than silently misread.

export function parseHeaders(text) {
  const rules = [];
  let current = null;
  text.split(/\r?\n/).forEach((raw, index) => {
    const line = raw.trimEnd();
    const where = `_headers line ${index + 1}`;
    if (!line.trim() || line.trim().startsWith('#')) return;
    if (!/^\s/.test(line)) {
      const pattern = line.trim();
      if (!pattern.startsWith('/') || pattern.includes(':') || pattern.split('*').length > 2) {
        throw new Error(`${where}: unsupported path pattern "${pattern}"`);
      }
      current = { pattern, set: [], unset: [], line: index + 1 };
      rules.push(current);
      return;
    }
    if (!current) throw new Error(`${where}: header line before any path`);
    const body = line.trim();
    if (body.startsWith('!')) {
      current.unset.push(body.slice(1).trim().toLowerCase());
      return;
    }
    const colon = body.indexOf(':');
    if (colon <= 0) throw new Error(`${where}: expected "Name: value"`);
    current.set.push([body.slice(0, colon).trim(), body.slice(colon + 1).trim()]);
  });
  return rules;
}

export function matchesPattern(pattern, pathname) {
  const star = pattern.indexOf('*');
  if (star === -1) return pattern === pathname;
  const prefix = pattern.slice(0, star);
  const suffix = pattern.slice(star + 1);
  return pathname.length >= prefix.length + suffix.length && pathname.startsWith(prefix) && pathname.endsWith(suffix);
}

// Headers for a request path, applying matching rules in file order: a rule's
// unsets first, then its values; a header already set by an earlier rule is appended to.
export function headersFor(rules, pathname) {
  const headers = new Map();
  const setByRule = new Set();
  for (const rule of rules) {
    if (!matchesPattern(rule.pattern, pathname)) continue;
    for (const name of rule.unset) headers.delete(name);
    for (const [name, value] of rule.set) {
      const key = name.toLowerCase();
      if (setByRule.has(key) && headers.has(key)) {
        headers.set(key, { name, value: `${headers.get(key).value}, ${value}` });
      } else {
        headers.set(key, { name, value });
        setByRule.add(key);
      }
    }
  }
  return headers;
}

// Header names set more than once, by one or several matching rules, for this path.
export function conflictingHeaders(rules, pathname) {
  const seen = new Set();
  const conflicts = new Set();
  for (const rule of rules) {
    if (!matchesPattern(rule.pattern, pathname)) continue;
    for (const [name] of rule.set) {
      const key = name.toLowerCase();
      if (seen.has(key)) conflicts.add(key);
      seen.add(key);
    }
  }
  return [...conflicts];
}

// Reads the subset of the host's _redirects format this site uses: comment lines and
// "source destination status" rules with exact paths (no splats or placeholders).
export function parseRedirects(text) {
  const rules = [];
  text.split(/\r?\n/).forEach((raw, index) => {
    const line = raw.trim();
    if (!line || line.startsWith('#')) return;
    const where = `_redirects line ${index + 1}`;
    const fields = line.split(/\s+/);
    if (fields.length !== 3) throw new Error(`${where}: expected "source destination status"`);
    const [from, to, status] = fields;
    if (!from.startsWith('/') || /[*:]/.test(from)) throw new Error(`${where}: the source must be an exact path`);
    if (!to.startsWith('/') || /[*:]/.test(to)) throw new Error(`${where}: the destination must be a site path`);
    if (!/^30[1278]$/.test(status)) throw new Error(`${where}: unsupported status ${status}`);
    rules.push({ from, to, status: Number(status), line: index + 1 });
  });
  return rules;
}
