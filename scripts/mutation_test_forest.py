#!/usr/bin/env python3
"""Check that the forest theorem's hypotheses and construction are load-bearing.

Every mutation must break `lake build ForestSolution`; the harmless edit must not.
"""
import atexit
import os
import pathlib
import signal
import subprocess
import sys

ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "ForestSolution.lean"

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
    ("barycentric coefficients only nonnegative",
     "lam_pos : \u2200 u j, j \u2208 N u \u2192 0 < lam u j",
     "lam_pos : \u2200 u j, j \u2208 N u \u2192 0 \u2264 lam u j"),
    ("balance condition broken",
     "lam_bal : \u2200 u, \u2211 j \u2208 N u, lam u j \u2022 (P j - P u) = 0",
     "lam_bal : \u2200 u, \u2211 j \u2208 N u, lam u j \u2022 (P j - P u) = P u"),
    ("rank inequality reversed (the forest hypothesis)",
     "rk_lt : \u2200 \u2983v p : V\u2984, parent v = some p \u2192 rk p < rk v",
     "rk_lt : \u2200 \u2983v p : V\u2984, parent v = some p \u2192 rk v < rk p"),
    ("accumulation sign flipped",
     "elim 0 fun p => potentialAux d n p + d p v",
     "elim 0 fun p => potentialAux d n p - d p v"),
    ("weights forget the rescaling",
     "  F.scale (fun a b => B.lam a b / B.lam b a) u * B.lam u j",
     "  B.lam u j"),
    ("the ratio is inverted",
     "noncomputable def w (u j : V) : \u211d :=\n  F.scale (fun a b => B.lam a b / B.lam b a) u * B.lam u j",
     "noncomputable def w (u j : V) : \u211d :=\n  F.scale (fun a b => B.lam b a / B.lam a b) u * B.lam u j"),
    ("scale_edge drops the ratio",
     "(h : F.parent v = some p) : F.scale c v = c p v * F.scale c p := by",
     "(h : F.parent v = some p) : F.scale c v = F.scale c p := by"),
    ("symmetry conclusion perturbed",
     "(h : F.parent v = some p) : B.w F p v = B.w F v p := by",
     "(h : F.parent v = some p) : B.w F p v = 2 * B.w F v p := by"),
    ("main theorem claims symmetry on every pair",
     "(\u2200 v p, p \u2208 N v \u2192 v \u2208 N p \u2192 F.parent v = some p \u2192 w p v = w v p) :=",
     "(\u2200 v p, p \u2208 N v \u2192 v \u2208 N p \u2192 w p v = w v p) :="),
]

HARMLESS = [
    ("docstring removal",
     "/-- The potential of `d`: the rank is always enough fuel. -/\n", ""),
]

def build() -> bool:
    """True when `lake build Solution` succeeds."""
    env = dict(os.environ, ELAN_HOME=os.environ.get(
        "ELAN_HOME", os.path.expanduser("~/.elan")))
    return subprocess.run(["lake", "build", "ForestSolution"], cwd=ROOT, env=env,
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
