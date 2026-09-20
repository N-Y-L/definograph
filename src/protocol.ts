/** Transport contract shared by the local workbench and future editor clients. */
export const PROTOCOL_VERSION = 2 as const;
export interface AnalysisOptions {
  inputMode?: 'term' | 'declaration';
  expansion?: { constants: string[]; maxDepth: number };
  previewDefinitions?: boolean;
}
export interface AnalysisRequest extends AnalysisOptions { source: string }
export const capabilities = {
  protocolVersion: PROTOCOL_VERSION,
  prover: 'lean',
  inputModes: ['term', 'declaration'],
  expansions: { maxConstants: 12, maxDepth: 3, policy: 'explicit-trusted-definitions', automaticPreviews: { maxDefinitions: 3, maxDepth: 1, maxBytes: 262144 } },
  source: { maxCharacters: 32_768, maxBytes: 65_536 },
  features: ['typed-expressions', 'declaration-signatures', 'bounded-expansion', 'scoped-fragments', 'semantic-document', 'automatic-view-planning', 'statement-reading-sequence', 'logical-overview', 'optional-readable-math', 'guided-reading-cues', 'compositional-set-constructions'],
  executesUserCommands: false,
} as const;
