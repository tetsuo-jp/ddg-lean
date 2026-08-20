import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Module.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# Positive discrete Laplacians over a forest of interior vertices

Wardetzky, Mathur, Kälberer and Grinspun show that not every triangle mesh
admits a discrete Laplace operator that is simultaneously symmetric, local,
linearly precise and positively weighted.  This file formalises a sufficient
condition for one to exist: **it is enough that the interior vertices span a
forest.**

The geometric input is that each interior vertex `u` lies in the interior of the
convex hull of its neighbours, so that there are positive `lam u j` with
`∑ j, lam u j • (P j - P u) = 0`.  Those coefficients are chosen one vertex at a
time and generally disagree on an edge joining two interior vertices.  The whole
content of the theorem is that the disagreement can be repaired by rescaling
each vertex's coefficients, and that a forest is exactly what makes the
rescaling consistent: on a tree the scale propagates from the root outwards,
while a cycle would impose a closing condition.

The forest hypothesis is taken in rooted form (`RootedForest`).  Every finite
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

namespace RootedForest

variable {V : Type} (F : RootedForest V)

/-- Accumulate `d` along the path to the root, with `n` steps of fuel. -/
noncomputable def potentialAux (d : V → V → ℝ) : ℕ → V → ℝ
  | 0, _ => 0
  | n + 1, v => (F.parent v).elim 0 fun p => potentialAux d n p + d p v

/-- The potential of `d`: the rank is always enough fuel. -/
noncomputable def potential (d : V → V → ℝ) (v : V) : ℝ :=
  F.potentialAux d (F.rk v) v

theorem potentialAux_root {d : V → V → ℝ} {v : V} (h : F.parent v = none) :
    ∀ n, F.potentialAux d n v = 0
  | 0 => rfl
  | _ + 1 => by simp [potentialAux, h]

theorem potential_root {d : V → V → ℝ} {v : V} (h : F.parent v = none) :
    F.potential d v = 0 := F.potentialAux_root h _

/-- One step of the accumulation. -/
theorem potentialAux_succ (d : V → V → ℝ) (n : ℕ) {v p : V} (h : F.parent v = some p) :
    potentialAux F d (n + 1) v = potentialAux F d n p + d p v := by
  simp [potentialAux, h]

/-- Any fuel at least the rank computes the same value. -/
theorem potentialAux_eq (d : V → V → ℝ) :
    ∀ n v, F.rk v ≤ n → potentialAux F d n v = F.potential d v := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro v hv
    cases hp : F.parent v with
    | none => rw [F.potentialAux_root hp, F.potential_root hp]
    | some p =>
      have hlt : F.rk p < F.rk v := F.rk_lt hp
      obtain ⟨m, hm⟩ : ∃ m, F.rk v = m + 1 := ⟨F.rk v - 1, by omega⟩
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
      have e1 : potentialAux F d n v = potentialAux F d k p + d p v := by
        rw [hk]; exact F.potentialAux_succ d k hp
      have e2 : F.potential d v = potentialAux F d m p + d p v := by
        rw [potential, hm]; exact F.potentialAux_succ d m hp
      rw [e1, e2, ih k (by omega) p (by omega), ih m (by omega) p (by omega)]

/-- **The defining property of the potential.**  Along every edge of the forest
the potential increases by exactly the prescribed amount. -/
theorem potential_edge {d : V → V → ℝ} {v p : V} (h : F.parent v = some p) :
    F.potential d v - F.potential d p = d p v := by
  have hlt : F.rk p < F.rk v := F.rk_lt h
  obtain ⟨m, hm⟩ : ∃ m, F.rk v = m + 1 := ⟨F.rk v - 1, by omega⟩
  have e : F.potential d v = potentialAux F d m p + d p v := by
    rw [potential, hm]; exact F.potentialAux_succ d m h
  rw [e, F.potentialAux_eq d m p (by omega)]; ring

/-- The positive scale attached to each vertex: the exponential of the potential
of `log c`.  Positivity is free, which is why the additive form is used. -/
noncomputable def scale (c : V → V → ℝ) (v : V) : ℝ :=
  Real.exp (F.potential (fun a b => Real.log (c a b)) v)

theorem scale_pos (c : V → V → ℝ) (v : V) : 0 < F.scale c v := Real.exp_pos _

/-- **The scale realises the prescribed ratio on every edge.** -/
theorem scale_edge {c : V → V → ℝ} {v p : V} (hc : 0 < c p v)
    (h : F.parent v = some p) : F.scale c v = c p v * F.scale c p := by
  have hpot : F.potential (fun a b => Real.log (c a b)) v
            - F.potential (fun a b => Real.log (c a b)) p = Real.log (c p v) :=
    F.potential_edge h
  unfold scale
  rw [← Real.exp_log hc, ← Real.exp_add]
  congr 1
  linarith

/-- The forest with no edges at all: every vertex is a root. -/
def empty (V : Type) : RootedForest V where
  parent _ := none
  rk _ := 0
  rk_lt := by intro v p h; simp at h

@[simp] theorem empty_parent (v : V) : (empty V).parent v = none := rfl

variable [DecidableEq V]

/-- The forest consisting of the single edge from `b` to `a`, with `a` the child. -/
def singleEdge {a b : V} (hab : a ≠ b) : RootedForest V where
  parent v := if v = a then some b else none
  rk v := if v = a then 1 else 0
  rk_lt := by
    intro v p h
    split at h
    · rename_i hv
      subst hv
      have hbp : b = p := Option.some.inj h
      subst hbp
      simp [Ne.symm hab]
    · exact absurd h (by simp)

@[simp] theorem singleEdge_parent_child {a b : V} (hab : a ≠ b) :
    (singleEdge hab).parent a = some b := by simp [singleEdge]


end RootedForest

/-! ## Barycentric data -/

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

namespace Bary

variable {P : V → E} {N : V → Finset V} (B : Bary P N) (F : RootedForest V)

/-- The repaired weights: each vertex's barycentric coefficients, rescaled. -/
noncomputable def w (u j : V) : ℝ :=
  F.scale (fun a b => B.lam a b / B.lam b a) u * B.lam u j

theorem w_pos {u j : V} (h : j ∈ N u) : 0 < B.w F u j :=
  mul_pos (F.scale_pos _ _) (B.lam_pos u j h)

/-- **(LIN).**  The repaired weights still balance every vertex. -/
theorem w_bal (u : V) : ∑ j ∈ N u, B.w F u j • (P j - P u) = 0 := by
  have h : ∑ j ∈ N u, B.w F u j • (P j - P u)
       = F.scale (fun a b => B.lam a b / B.lam b a) u •
           ∑ j ∈ N u, B.lam u j • (P j - P u) := by
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [w, smul_smul]
  rw [h, B.lam_bal u, smul_zero]

/-- **Positive row sums**, the nondegeneracy condition of Wardetzky et al. -/
theorem w_sum_pos {u : V} (h : (N u).Nonempty) : 0 < ∑ j ∈ N u, B.w F u j :=
  Finset.sum_pos (fun j hj => B.w_pos F hj) h

/-- **(SYM) across an edge of the forest.**  This is the point of the rescaling:
the two vertices of an interior edge assign it the same weight. -/
theorem w_symm {v p : V} (hv : p ∈ N v) (hp : v ∈ N p)
    (h : F.parent v = some p) : B.w F p v = B.w F v p := by
  have hlp : 0 < B.lam p v := B.lam_pos p v hp
  have hlv : 0 < B.lam v p := B.lam_pos v p hv
  have hs : F.scale (fun a b => B.lam a b / B.lam b a) v
          = B.lam p v / B.lam v p * F.scale (fun a b => B.lam a b / B.lam b a) p :=
    F.scale_edge (div_pos hlp hlv) h
  unfold w
  rw [hs]
  field_simp

end Bary

/-! ## The theorem -/

/-- **A forest of interior vertices suffices.**  Given barycentric coefficients at
each vertex (which the geometry provides, every interior vertex lying inside the
convex hull of its neighbours) and a rooted forest structure on the vertices,
there are weights that are positive on every edge, balance every vertex, have
positive row sums, and agree from both ends of every forest edge.

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
  ⟨B.w F, fun _ _ h => B.w_pos F h, B.w_bal F, fun _ h => B.w_sum_pos F h,
    fun _ _ hv hp h => B.w_symm F hv hp h⟩

/-! ## The cases that a mesh with at most two interior vertices needs

A triangulation of at most five points has at most two interior vertices, so the
subgraph they span has at most one edge.  Those two cases are instantiated here,
so that the statement "at most one interior edge suffices" needs no graph theory
at all. -/

/-- **No interior edge.**  Each vertex is scaled on its own. -/
theorem exists_good_weights_of_no_edge {P : V → E} {N : V → Finset V} (B : Bary P N) :
    ∃ w : V → V → ℝ,
      (∀ u j, j ∈ N u → 0 < w u j) ∧
      (∀ u, ∑ j ∈ N u, w u j • (P j - P u) = 0) ∧
      (∀ u, (N u).Nonempty → 0 < ∑ j ∈ N u, w u j) :=
  ⟨B.w (RootedForest.empty V), fun _ _ h => B.w_pos _ h, B.w_bal _,
    fun _ h => B.w_sum_pos _ h⟩

/-- **One interior edge.**  The two ends of that edge agree on its weight.  This
is the case a triangulation of at most five points is in. -/
theorem exists_good_weights_of_one_edge [DecidableEq V] {P : V → E} {N : V → Finset V}
    (B : Bary P N) {a b : V} (hab : a ≠ b) (hb : b ∈ N a) (ha : a ∈ N b) :
    ∃ w : V → V → ℝ,
      (∀ u j, j ∈ N u → 0 < w u j) ∧
      (∀ u, ∑ j ∈ N u, w u j • (P j - P u) = 0) ∧
      (∀ u, (N u).Nonempty → 0 < ∑ j ∈ N u, w u j) ∧
      w b a = w a b :=
  ⟨B.w (RootedForest.singleEdge hab), fun _ _ h => B.w_pos _ h, B.w_bal _,
    fun _ h => B.w_sum_pos _ h,
    B.w_symm _ hb ha (RootedForest.singleEdge_parent_child hab)⟩


end LapForest
