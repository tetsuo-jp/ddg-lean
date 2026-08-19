# Discrete differential geometry in Lean 4

Two self-contained formalizations, each prepared as a
[Palomar registry](https://palomar-registry.org/) entry.

## 1. Discrete Gauss–Bonnet for closed triangulated surfaces

The total angle defect of a closed triangulated surface equals `2π · χ`:

```lean
theorem sum_defect_eq_two_pi_mul_euler :
    ∑ v, T.defect v = 2 * π * (T.euler : ℝ)
```

with the tetrahedron (`4π`) as the smallest instance.  The point of isolating
this form is that it needs no geometry beyond *the angles of a face sum to `π`*:
everything else is finite bookkeeping.  In particular `3·#F = 2·#E` is **not**
assumed — it is derived by double counting from "every face has three vertices"
and "every edge lies in exactly two faces".

Nothing here is new mathematics; the result is classical (Descartes, Banchoff).
This repository is a formalization, prepared for the
[Palomar registry](https://palomar-registry.org/).

## 2. The cotangent formula, and linear precision of the cotangent Laplacian

```lean
theorem cotan_form (hp : sarea2 p ≠ 0) (g : E2) :
    Real.cot (angle0 p) * inner ℝ g (e0 p) ^ 2
  + Real.cot (angle1 p) * inner ℝ g (e1 p) ^ 2
  + Real.cot (angle2 p) * inner ℝ g (e2 p) ^ 2
      = |sarea2 p| * ‖g‖ ^ 2
```

the identity behind the cotangent Laplacian.  The gradient is characterised
without calculus: `g` is the gradient of the affine interpolant exactly when
`⟪g, pᵢ - pⱼ⟫` is the jump of `u` along that edge.  `inner_form` is the same
identity with each `cot θₖ * 2A` replaced by an inner product of edges, and
needs no hypotheses at all.  The whole geometric content is `gram_two`: the
Gram matrix of three vectors of the plane is singular.

Summing this around a closed one-ring gives **linear precision**, property
(LIN) of Wardetzky–Mathur–Kälberer–Grinspun:

```lean
theorem linear_precision {n : ℕ} [NeZero n] (p : E2) (q : ZMod n → E2)
    (h : ∀ j : ZMod n, 0 < cross (q j - p) (q (j + 1) - p)) :
    ∑ j : ZMod n, (cotCorner p (q j) (q (j + 1)) • (q j - p)
                 + cotCorner p (q (j + 1)) (q j) • (q (j + 1) - p)) = 0
```

The proof is one identity per triangle plus a telescoping sum: each triangle's
two weighted edge vectors add up to a quarter turn of the opposite edge, and the
quarter turns cancel because the ring closes.

Also classical (Pinkall–Polthier, Duffin, MacNeal, Wardetzky et al.).

## 3. A forest of interior vertices suffices for a positive Laplacian

Wardetzky et al. show that not every mesh admits an operator that is at once
symmetric, local, linearly precise and positively weighted.  A sufficient
condition for one to exist is that the **interior vertices span a forest**:

```lean
theorem exists_good_weights {P : V → E} {N : V → Finset V}
    (B : Bary P N) (F : RootedForest V) :
    ∃ w : V → V → ℝ, (∀ u j, j ∈ N u → 0 < w u j) ∧ …
```

Each interior vertex lies inside the convex hull of its neighbours, so it has
positive barycentric coefficients; those are chosen one vertex at a time and
disagree on interior edges.  The whole content is that the disagreement can be
repaired by rescaling, and that a forest is exactly what makes the rescaling
consistent, since a cycle would impose a closing condition.

⚠ The forest hypothesis is taken in **rooted** form, and the geometric fact
supplying the barycentric data is assumed rather than derived.  See
`formalization-forest.yaml` for the full list of gaps.  **No priority is
claimed**: the argument is elementary and may well be folklore.

## Layout

| file | contents |
|---|---|
| `Challenge.lean` / `Solution.lean` | entry 1: statements (with `sorry`) and proofs |
| `CotanChallenge.lean` / `CotanSolution.lean` | entry 2: the same, for the cotangent formula |
| `Audit.lean`, `CotanAudit.lean` | `#print axioms` for every claimed theorem |
| `comparator.json`, `comparator-cotan.json` | the theorem names compared by [Comparator](https://github.com/leanprover/comparator) |
| `formalization.yaml`, `formalization-cotan.yaml` | Palomar metadata, schema v0.4 |
| `scripts/audit.sh` | the five trust conditions for both entries, fails closed |
| `ForestChallenge.lean` / `ForestSolution.lean` | entry 3: the forest condition |
| `scripts/mutation_test*.py` | check that hypotheses and constants are load-bearing |

## A note on `ring`

`gram_two` is a polynomial identity in six real variables.  Expanding the inner
products into coordinates and calling `ring` costs **262 s and 5 GB**, and the
three-point form did not finish in ten minutes.  Keeping the inner products
opaque and handing `ring` only the Lagrange and Binet–Cauchy identities — each
of which *is* cheap in coordinates — brings the whole module to **14 s**.  If a
`ring` call is taking minutes, the fix is usually to give it smaller atoms
rather than more time.

## Building

```sh
lake exe cache get
lake build Challenge Solution Audit CotanChallenge CotanSolution CotanAudit
./scripts/audit.sh
```

Lean `v4.31.0`, Mathlib pinned in `lake-manifest.json`.

## What the audit checks

1. `Challenge.olean` and `Solution.olean` are produced.
2. Every claimed theorem depends on exactly `propext`, `Classical.choice`,
   `Quot.sound` — no others.
3. No `sorry`, `native_decide`, `unsafe` or project-defined `axiom` in either
   solution module; exactly four deliberate `sorry` holes in each challenge.
4. The claimed theorems appear in both modules of each pair.
5. **Mutation test**: thirty-three single-token changes to the structures'
   fields and to the constants in the claimed statements each break the build,
   and four harmless edits do not.

The mutation scripts are crash-safe: they copy the source aside before the
first mutation, restore it on every exit path including `SIGTERM`, and recover
at start-up if a previous run was killed before it could restore.  This is not
hypothetical.  A ten-minute timeout once killed the audit mid-mutation and left
two files mutated, after which the next run reported failures that had nothing
to do with the code.

Point 5 is there because a correct proof of a badly stated theorem still passes
points 1–4.  An earlier version of this development assumed `3·#F = 2·#E` as a
field of the structure; the mutation test then showed that "every face has three
vertices" was used by no proof at all.  The structure was reworked so that the
relation is derived and every field is load-bearing.

## Scope and limitations

**Entry 1.** The angles are abstract real data constrained only by summing to `π` on each
face.  Nothing embeds the surface in Euclidean space or derives the angles from
edge lengths, and the angles are not required to be positive.  `euler` is
defined as `#V − #E + #F` from the data and is not connected to any topological
invariant here.  Orientability and connectedness are neither assumed nor needed.

**Entry 2.** The gradient is never constructed and no integral is taken: `g` is
constrained only by the inner products appearing in the statements, so the
"Dirichlet energy" reading is supplied by the reader.  Only the plane is
treated.  One point worth flagging: the hypothesis `sarea2 p ≠ 0` of
`cotan_form` is **not** needed for the statement to be true — at a degenerate
triangle every interior angle is `0`, `π` or `π/2`, and Lean's `Real.cot` is `0`
at all three because `x / 0 = 0`, so both sides vanish.  It is kept deliberately,
because without it the degenerate case asserts a junk value rather than a fact
about triangles.  The mutation test shows only that the *proof* uses it.

Full metadata, sources and limitations: `formalization.yaml`,
`formalization-cotan.yaml`.
