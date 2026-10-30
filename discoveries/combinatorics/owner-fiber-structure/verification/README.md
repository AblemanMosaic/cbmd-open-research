# Verification boundary

`owner_fiber.py` is standard-library only and imports nothing from the archive.
It rebuilds the source row from the integer amplitude and the Lagrange assembly,
then checks the three parts of the claim, each with an adverse control.

It is a check of the **finite model** of the owner-fiber statement. It does not
bind the packed source definitions, does not model multiple blocks, and proves
nothing about native execution or novelty.

## The degeneracy gate

With `A = 0` and `R >= |D(u)|` every off-diagonal source row is identically
zero, so the unique-contributor statement holds vacuously and the box tests
nothing. That was the defect in the predecessor evidence. The run therefore
fails unless off-diagonal contributors actually occur, and it separately
confirms that the known defect regime still reproduces as degenerate.

A second, subtler degeneracy was caught while writing this file: a parameter box
can be non-degenerate while the *layouts* still produce no off-diagonal
contributor, because if every owner carries the target's own head word then the
only orbit element with that head is the target itself. Head words are now
required to cover the head-word space, with a surplus owner duplicating a head
so that distinct owners with equal heads — the case the owner check exists to
handle — are exercised.
