// Strings that must never reach a published byte. The build and the checks share these.

// Local machine paths and names. Placeholder paths such as /absolute/path/to/... in the
// setup guide are instructions, not machine paths, and do not match.
// A path must start there: "result/home/telescope" (an internal node path) is not a home
// directory, "/home/alice" is.
export const PRIVATE_PATHS = [
  [/(?<![\w.-])\/Users\/[^/\s"'<>]+/, 'macOS home directory path'],
  [/(?<![\w.-])\/home\/[a-z][^/\s"'<>]*/, 'Linux home directory path'],
  [/(?<![\w.-])\/private\/(?:tmp|var|etc)\b/, 'macOS private system path'],
  [/(?<![\w.~-])\/tmp\//, 'temporary directory path'],
  [/(?<![\w.-])\/var\/folders\//, 'macOS temporary folder path'],
  [/\b[A-Za-z]:\\/, 'Windows drive path'],
  [/\bfile:\/\//i, 'file URL'],
  [/sourceMappingURL/i, 'source map reference'],
];

// Additional patterns for recorded-view files (fragments, their stylesheet and sources).
// These files come from a capture pipeline, so identifiers of runs, sessions, requests or
// private captures must not survive into them. Commit hashes shown by the site itself are
// added by the build, never taken from a fragment.
export const RECORDED_VIEW_PATTERNS = [
  ...PRIVATE_PATHS,
  [/\.local\//, 'reference to a local runtime directory'],
  [/localhost|127\.0\.0\.1|0\.0\.0\.0|\[::1\]/i, 'local service address'],
  [/[\w.+-]+@[\w-]+\.[\w.-]+/, 'email address'],
  [/\b[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}\b/i, 'UUID (session, request or capture identifier)'],
  // At least one letter, so a long decimal literal in a Lean term is not mistaken for a hash.
  [/\b(?=[0-9a-f]*[a-f])[0-9a-f]{32,}\b/i, 'long hexadecimal identifier (hash or run id)'],
];

// Recorded fragments also may not carry short hexadecimal identifiers such as an attempt or
// capture id shown in a panel ("attempt 1 (19da1ecd)"). Colour values (#…) and words without
// both a digit and a letter are not affected.
export const FRAGMENT_PATTERNS = [
  ...RECORDED_VIEW_PATTERNS,
  [/(?<![#\w-])(?=[0-9a-f]*\d)(?=[0-9a-f]*[a-f])[0-9a-f]{7,31}(?![\w-])/i, 'short hexadecimal identifier (attempt, capture or commit id)'],
];

// Returns the labels of every pattern found in text.
export function findPrivate(text, patterns = PRIVATE_PATHS) {
  return patterns.filter(([pattern]) => pattern.test(text)).map(([, label]) => label);
}
