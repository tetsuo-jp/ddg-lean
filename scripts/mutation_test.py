#!/usr/bin/env python3
"""Check that the claimed statements are load-bearing.

Each mutation below changes one field of the structure or one constant in a
claimed statement.  Every mutation must make `lake build Solution` fail; the two
harmless edits must leave it passing.  A mutation that passes means the
hypothesis it touches is dead weight, which is a defect in the *statement* even
when every proof is correct.
"""
import atexit
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "Solution.lean"

# --- crash safety -----------------------------------------------------------
# A killed run must not leave a mutation in the working tree.  It happened: a
# ten-minute timeout killed this script mid-mutation and left two files mutated,
# after which the next audit reported failures that had nothing to do with the
# code.  The original is copied aside before the first mutation, restored on
# every exit path including SIGTERM and SIGINT, and recovered at start-up if a
# previous run was killed before it could restore.
BACKUP = SRC.with_suffix(SRC.suffix + ".mutation-backup")


def _restore() -> None:
    if BACKUP.exists():
        SRC.write_text(BACKUP.read_text())
        BACKUP.unlink()


def _on_signal(signum, _frame):
    _restore()
    raise SystemExit(128 + signum)


def install_guards() -> None:
    if BACKUP.exists():
        print(f"recovering {SRC.name} from {BACKUP.name}: a previous run was killed")
        _restore()
    BACKUP.write_text(SRC.read_text())
    atexit.register(_restore)
    for s in (signal.SIGTERM, signal.SIGINT, signal.SIGHUP):
        signal.signal(s, _on_signal)


MUTATIONS = [
    ("tetrahedron defect 4pi -> 3pi",
     "∑ v, T.defect v = 4 * π := by", "∑ v, T.defect v = 3 * π := by"),
    ("face contribution -pi*F -> +pi*F",
     "- π * (Fintype.card F : ℝ) := by", "+ π * (Fintype.card F : ℝ) := by"),
    ("Euler characteristic -E -> +E",
     "(Fintype.card V : ℤ) - (T.edgeSet.card : ℤ)",
     "(Fintype.card V : ℤ) + (T.edgeSet.card : ℤ)"),
    ("defect 2pi -> pi",
     "2 * π - ∑ f, T.angle f v", "π - ∑ f, T.angle f v"),
    ("angle sum of a face pi -> 2pi",
     "angle_sum : ∀ f, ∑ v ∈ verts f, angle f v = π",
     "angle_sum : ∀ f, ∑ v ∈ verts f, angle f v = 2 * π"),
    ("angle_eq_zero made vacuous",
     "angle_eq_zero : ∀ f v, v ∉ verts f → angle f v = 0",
     "angle_eq_zero : ∀ f v, v ∉ verts f → angle f v = angle f v"),
    ("faces are triangles 3 -> 4",
     "card_verts : ∀ f, (verts f).card = 3",
     "card_verts : ∀ f, (verts f).card = 4"),
    ("closedness: two faces per edge 2 -> 3",
     "two_faces : ∀ e ∈ edgeSet, #{f | e ⊆ verts f} = 2",
     "two_faces : ∀ e ∈ edgeSet, #{f | e ⊆ verts f} = 3"),
    ("edges have two endpoints 2 -> 3",
     "mem_edgeSet : ∀ e, e ∈ edgeSet ↔ (e.card = 2 ∧ ∃ f, e ⊆ verts f)",
     "mem_edgeSet : ∀ e, e ∈ edgeSet ↔ (e.card = 3 ∧ ∃ f, e ⊆ verts f)"),
    ("double count 3F = 2E -> 3F = 3E",
     "3 * Fintype.card F = 2 * T.edgeSet.card := by",
     "3 * Fintype.card F = 3 * T.edgeSet.card := by"),
    ("tetrahedron edge count 6 -> 7",
     "T.edgeSet.card = 6 := by", "T.edgeSet.card = 7 := by"),
]

HARMLESS = [
    ("bound variable renaming",
     "noncomputable def defect (v : V) : ℝ :=\n  2 * π - ∑ f, T.angle f v",
     "noncomputable def defect (w : V) : ℝ :=\n  2 * π - ∑ g, T.angle g w"),
    ("docstring removal",
     "/-- The Euler characteristic `#V - #E + #F`. -/\n", ""),
]


def build() -> bool:
    """True when `lake build Solution` succeeds."""
    env = dict(os.environ, ELAN_HOME=os.environ.get(
        "ELAN_HOME", os.path.expanduser("~/.elan")))
    return subprocess.run(["lake", "build", "Solution"], cwd=ROOT, env=env,
                          capture_output=True, text=True).returncode == 0


def main() -> int:
    install_guards()
    original = SRC.read_text()
    failures = []
    try:
        for name, before, after in MUTATIONS:
            if before not in original:
                failures.append(f"mutation not applicable: {name}")
                continue
            SRC.write_text(original.replace(before, after, 1))
            if build():
                failures.append(f"mutation SURVIVED (hypothesis is dead): {name}")
            else:
                print(f"  detected  {name}")
        for name, before, after in HARMLESS:
            if before not in original:
                failures.append(f"harmless edit not applicable: {name}")
                continue
            SRC.write_text(original.replace(before, after, 1))
            if build():
                print(f"  no false positive  {name}")
            else:
                failures.append(f"harmless edit broke the build: {name}")
    finally:
        SRC.write_text(original)
        _restore()

    if failures:
        print("\nMUTATION TEST FAILED")
        for f in failures:
            print("  " + f)
        return 1
    print(f"\nMUTATION OK ({len(MUTATIONS)} detected, "
          f"{len(HARMLESS)} harmless edits survived)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
