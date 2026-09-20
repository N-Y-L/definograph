import type { EditorRange } from '../../server/editor-context.js';
export interface EditorDocument { uri: string; version: number; fileName: string; selection: EditorRange }
export interface Ticket { requestId: string; document: EditorDocument; signal: AbortSignal }
/** A diagram belongs to exactly one buffer version and selection. */
export class EditorAnalysisLifecycle {
  #counter = 0;
  #controller?: AbortController;
  #ticket?: Ticket;
  begin(document: EditorDocument): Ticket {
    this.#controller?.abort();
    this.#controller = new AbortController();
    this.#ticket = { requestId: String(++this.#counter), document: structuredClone(document), signal: this.#controller.signal };
    return this.#ticket;
  }
  current(): Ticket | undefined { return this.#ticket; }
  accepts(ticket: Ticket): boolean { return this.#ticket === ticket && !ticket.signal.aborted; }
  invalidate(uri?: string): Ticket | undefined {
    if (uri && this.#ticket?.document.uri !== uri) return undefined;
    this.#controller?.abort();
    return this.#ticket;
  }
  dispose(): void { this.invalidate(); this.#ticket = undefined; }
}
