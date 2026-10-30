# Verification boundary

`separation.py` is standard-library only and imports nothing from the archive.
It recomputes the amplitude from the defining parity construction as well as
from the closed form and requires the two to agree before reporting anything.

It establishes facts about the **reference amplitude family**. It does not
reproduce the inherited selected-degree-six source fixture, does not bind any
native source definition, and makes no SAT or novelty claim. Its content gates
fail the run if the separation box is degenerate, if the Kummer control breaks,
or if a low-digit criterion turns out to exist after all.
