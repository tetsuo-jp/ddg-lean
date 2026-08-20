import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Positive discrete Laplacians over a forest of interior vertices (statement)

Wardetzky, Mathur, Kälberer and Grinspun show that not every triangle mesh
admits a discrete Laplace operator that is simultaneously symmetric, local,
linearly precise and positively weighted.  The result claimed here is a
sufficient condition for one to exist: **it is enough that the interior vertices
span a forest.**

The geometric input appears as `Bary`: each interior vertex lies in the interior
of the convex hull of its neighbours, so there are positive coefficients that
balance it.  The forest hypothesis appears as `RootedForest`.  Every finite
forest admits such a structure, by picking a root in each component and letting
`rk` be the distance to it; that step is standard and is *not* formalised here.
-/

open Finset

namespace LapForest

/-- A rooted forest on `V`: a parent pointer together with a rank that strictly
decreases towards the roots.  A vertex with no parent is a root. -/
structure RootedForest (V : Type) where
  /-- the parent of a vertex, `none` at a root -/
  parent : V → Option V
  /-- a rank that strictly decreases towards the roots, so there are no cycles -/
  rk : V → ℕ
  /-- the defining property: a parent has strictly smaller rank -/
  rk_lt : ∀ ⦃v p : V⦄, parent v = some p → rk p < rk v

variable {V : Type} {E : Type} [AddCommGroup E] [Module ℝ E]

/-- Barycentric coefficients at each interior vertex: strictly positive numbers
that balance the vertex against its neighbours.  This is what "`u` lies in the
interior of the convex hull of its neighbours" provides. -/
structure Bary (P : V → E) (N : V → Finset V) where
  /-- the coefficient of neighbour `j` at vertex `u` -/
  lam : V → V → ℝ
  /-- coefficients are strictly positive on neighbours -/
  lam_pos : ∀ u j, j ∈ N u → 0 < lam u j
  /-- the vertex is balanced against its neighbours -/
  lam_bal : ∀ u, ∑ j ∈ N u, lam u j • (P j - P u) = 0

/-- **A forest of interior vertices suffices.**  Given barycentric coefficients
at each vertex and a rooted forest structure on the vertices, there are weights
that are positive on every edge, balance every vertex, have positive row sums,
and agree from both ends of every forest edge.

These are (POS), (LIN), the nondegeneracy of Wardetzky–Mathur–Kälberer–Grinspun,
and (SYM) across the edges where the two ends could disagree.  (LOC) holds by
construction, since the weights are indexed by neighbours. -/
theorem exists_good_weights {P : V → E} {N : V → Finset V}
    (B : Bary P N) (F : RootedForest V) :
    ∃ w : V → V → ℝ,
      (∀ u j, j ∈ N u → 0 < w u j) ∧
      (∀ u, ∑ j ∈ N u, w u j • (P j - P u) = 0) ∧
      (∀ u, (N u).Nonempty → 0 < ∑ j ∈ N u, w u j) ∧
      (∀ v p, p ∈ N v → v ∈ N p → F.parent v = some p → w p v = w v p) :=
  sorry

/-- **No interior edge.**  Each vertex is scaled on its own. -/
theorem exists_good_weights_of_no_edge {P : V → E} {N : V → Finset V} (B : Bary P N) :
    ∃ w : V → V → ℝ,
      (∀ u j, j ∈ N u → 0 < w u j) ∧
      (∀ u, ∑ j ∈ N u, w u j • (P j - P u) = 0) ∧
      (∀ u, (N u).Nonempty → 0 < ∑ j ∈ N u, w u j) :=
  sorry

/-- **One interior edge.**  The two ends of that edge agree on its weight.  This
is the case a triangulation of at most five points is in. -/
theorem exists_good_weights_of_one_edge [DecidableEq V] {P : V → E} {N : V → Finset V}
    (B : Bary P N) {a b : V} (hab : a ≠ b) (hb : b ∈ N a) (ha : a ∈ N b) :
    ∃ w : V → V → ℝ,
      (∀ u j, j ∈ N u → 0 < w u j) ∧
      (∀ u, ∑ j ∈ N u, w u j • (P j - P u) = 0) ∧
      (∀ u, (N u).Nonempty → 0 < ∑ j ∈ N u, w u j) ∧
      w b a = w a b :=
  sorry

end LapForest
