import { useEffect, useId, useRef, type ReactNode } from 'react';

/** Native dialog supplies focus containment, Escape, and focus restoration. */
export function Drawer({ open, title, side = 'right', onClose, children }: {
  open: boolean; title: string; side?: 'left' | 'right'; onClose: () => void; children: ReactNode;
}) {
  const dialog = useRef<HTMLDialogElement>(null);
  const titleId = useId();
  useEffect(() => {
    const node = dialog.current;
    if (!node) return;
    if (!open) { if (node.open) node.close(); return; }
    if (!node.open) node.showModal();
    const previousOverflow = document.body.style.overflow;
    document.body.style.overflow = 'hidden';
    return () => { document.body.style.overflow = previousOverflow; };
  }, [open]);
  return <dialog ref={dialog} className={`atlas-drawer atlas-drawer-${side}`} aria-labelledby={titleId}
    onCancel={onClose} onClose={() => { if (open) onClose(); }} onClick={event => { if (event.target === event.currentTarget) onClose(); }}>
    <div className="drawer-surface">
      <header className="drawer-heading"><h2 id={titleId}>{title}</h2><button type="button" className="drawer-close" onClick={onClose} aria-label={`Close ${title}`}>×</button></header>
      {open && children}
    </div>
  </dialog>;
}
