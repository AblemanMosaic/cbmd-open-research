# Low-sector grid audit

This directory contains a second-reader audit of what the existing exact-model grid can actually detect.

The audit deliberately reuses [`low_sector_pairing_core.js`](../../explorer/source/low_sector_pairing_core.js) rather than presenting itself as an independent derivation. It therefore audits the implemented model and the evidentiary reach of its tests; it does not validate the unresolved geometric premises.

From the repository root, run:

```text
node discoveries/ech/genus-two-low-sector/verification/grid-audit/grid_audit.js
node discoveries/ech/genus-two-low-sector/verification/grid-audit/distinguishing_sources.js
```

The first command recomputes the audit in memory and requires exact equality with `grid_audit.json`. The second prints representative lists of the fifteen sector-one sources that distinguish the valid operator from the deliberately invalid junction deletion.

Read [`LOW_SECTOR_GRID_AUDIT.md`](LOW_SECTOR_GRID_AUDIT.md) for the interpretation and limitations.
