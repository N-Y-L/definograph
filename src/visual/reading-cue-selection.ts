import type { ReadingCue, ReadingCuePlan } from '../reading/cues';
import type { SemanticDocument } from '../semantic/types';

/** Attention in one exact document. IDs alone are not identities across captures. */
export interface ReadingCueSelection {
  readonly document: SemanticDocument;
  readonly cueId: string;
  /** A source node of the cue; grouped introductions can include several nodes. */
  readonly nodeId: string;
  readonly relationId?: string;
}

export function createReadingCueSelection(document: SemanticDocument, cue: ReadingCue, nodeId = cue.nodeId): ReadingCueSelection {
  return { document, cueId: cue.id, nodeId, relationId: cue.stage.relationId };
}

interface CueResolution {
  readonly plan: ReadingCuePlan;
  readonly document: SemanticDocument;
  readonly selectedNodeId: string;
  readonly rootNodeId: string;
  readonly selectedRelationId?: string;
  readonly selection?: ReadingCueSelection | null;
}

/** Restore an exact stage only while its document and selected source still agree.
 * Explicit relation/node selections take precedence over retained attention. */
export function resolveReadingCue({ plan, document, selectedNodeId, rootNodeId, selectedRelationId, selection }: CueResolution): ReadingCue | undefined {
  const relationCue = selectedRelationId ? plan.cues.find(cue => cue.stage.relationId === selectedRelationId
    && (selectedNodeId === rootNodeId || cue.sourceNodeIds.includes(selectedNodeId))) : undefined;
  if (relationCue) return relationCue;
  const retained = selection?.document === document && (!selectedRelationId || selection.relationId === selectedRelationId)
    ? plan.cues.find(cue => cue.id === selection.cueId && cue.sourceNodeIds.includes(selection.nodeId)
      && cue.sourceNodeIds.includes(selectedNodeId) && cue.stage.relationId === selection.relationId)
    : undefined;
  return retained ?? plan.cues.find(cue => cue.sourceNodeIds.includes(selectedNodeId))
    ?? (selectedNodeId === rootNodeId ? plan.cues[0] : undefined);
}

export interface ReadingCueSelectionCallbacks {
  readonly onNodeSelect?: (id: string) => void;
  readonly onSourceSelect?: (id: string) => void;
  readonly onCueChange?: (selection: ReadingCueSelection | null) => void;
}

/** Keep node/source notifications in their existing order. Publish the cue last,
 * so a caller can reset attention in onNodeSelect before retaining this stage. */
export function notifyReadingCueSelection(selection: ReadingCueSelection, callbacks: ReadingCueSelectionCallbacks): void {
  callbacks.onNodeSelect?.(selection.nodeId);
  callbacks.onSourceSelect?.(selection.relationId ?? selection.nodeId);
  callbacks.onCueChange?.(selection);
}
