"""Exact, standard-library reference tools for the CBMD complexity experiment.

Python audit results are finite evidence.  The corresponding general theorems
are the separately compiled Lean sources, not a consequence of importing this
package.  This package is project-authored, not external independent review.
"""

from .model import (
    BCM1Counts,
    BCM1Result,
    UniversalState,
    active_set,
    joint_entry,
    master_numerator,
    mismatches,
    orbit_compatible,
    swap_positions,
)

__all__ = [
    "BCM1Counts", "BCM1Result", "UniversalState", "active_set", "joint_entry",
    "master_numerator", "mismatches", "orbit_compatible", "swap_positions",
]
