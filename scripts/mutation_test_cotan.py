#!/usr/bin/env python3
"""Check that the claimed cotangent statements are load-bearing.

Every mutation below must break `lake build CotanSolution`; the harmless edit
must not.

One caveat this test cannot settle by itself, recorded in
formalization-cotan.yaml: the last mutation shows only that the *proof* of
`cotan_form` uses the nondegeneracy hypothesis.  The *statement* is true
without it, because at a degenerate triangle every interior angle is 0, pi or
pi/2 and Lean's `Real.cot` is 0 at all three (`x / 0 = 0`).  The hypothesis is
kept deliberately.
"""
import atexit
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "CotanSolution.lean"

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
    ("gram_two coefficient 2 -> 3",
     "- 2 * inner ℝ u v * inner ℝ g u * inner ℝ g v",
     "- 3 * inner ℝ u v * inner ℝ g u * inner ℝ g v"),
    ("cross product sign",
     "def cross (a b : E2) : ℝ := a 0 * b 1 - a 1 * b 0",
     "def cross (a b : E2) : ℝ := a 0 * b 1 + a 1 * b 0"),
    ("signed area sign",
     "(p 1 0 - p 0 0) * (p 2 1 - p 0 1) - (p 2 0 - p 0 0) * (p 1 1 - p 0 1)",
     "(p 1 0 - p 0 0) * (p 2 1 - p 0 1) + (p 2 0 - p 0 0) * (p 1 1 - p 0 1)"),
    ("Lagrange identity + -> -",
     "‖a‖ ^ 2 * ‖b‖ ^ 2 = inner ℝ a b ^ 2 + cross a b ^ 2",
     "‖a‖ ^ 2 * ‖b‖ ^ 2 = inner ℝ a b ^ 2 - cross a b ^ 2"),
    ("cotan_form right side loses the absolute value",
     "      = |sarea2 p| * ‖g‖ ^ 2 := by", "      = sarea2 p * ‖g‖ ^ 2 := by"),
    ("angle at vertex 1 taken at the wrong vertex",
     "noncomputable def angle1 : ℝ := angle (p 2 - p 1) (p 0 - p 1)",
     "noncomputable def angle1 : ℝ := angle (p 2 - p 0) (p 0 - p 1)"),
    ("edge e1 reversed",
     "def e1 : E2 := p 0 - p 2", "def e1 : E2 := p 2 - p 0"),
    ("inner_form exponent 2 -> 3",
     "* inner ℝ g (e0 p) ^ 2\n    - inner ℝ (e0 p) (e2 p)",
     "* inner ℝ g (e0 p) ^ 3\n    - inner ℝ (e0 p) (e2 p)"),
    ("quarter turn rotL loses a sign",
     "toFun a := EuclideanSpace.single 0 (-a 1) + EuclideanSpace.single 1 (a 0)",
     "toFun a := EuclideanSpace.single 0 (a 1) + EuclideanSpace.single 1 (a 0)"),
    ("corner weight taken at the wrong corner",
     "noncomputable def cotCorner (a b c : E2) : \u211d := Real.cot (angle (a - c) (b - c))",
     "noncomputable def cotCorner (a b c : E2) : \u211d := Real.cot (angle (a - b) (b - c))"),
    ("linear precision one-ring shifted by two",
     "cotCorner p (q j) (q (j + 1)) \u2022 (q j - p)\n                 + cotCorner p (q (j + 1)) (q j) \u2022 (q (j + 1) - p)) = 0 := by",
     "cotCorner p (q j) (q (j + 2)) \u2022 (q j - p)\n                 + cotCorner p (q (j + 1)) (q j) \u2022 (q (j + 1) - p)) = 0 := by"),
    ("corner_pair_inner right side loses the cross factor",
     "= cross (b - a) (c - a) \u2022 rotL (b - c) := by",
     "= rotL (b - c) := by"),
    ("nondegeneracy hypothesis weakened",
     "theorem cotan_form (hp : sarea2 p ≠ 0) (g : E2) :",
     "theorem cotan_form (hp : sarea2 p ≠ 0 ∨ True) (g : E2) :"),
]

HARMLESS = [
    ("docstring removal",
     "/-- The scalar cross product of two vectors of the plane. -/\n", ""),
]

def build() -> bool:
    """True when `lake build Solution` succeeds."""
    env = dict(os.environ, ELAN_HOME=os.environ.get(
        "ELAN_HOME", os.path.expanduser("~/.elan")))
    return subprocess.run(["lake", "build", "CotanSolution"], cwd=ROOT, env=env,
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
