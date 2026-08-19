# Discrete Gauss–Bonnet for closed triangulated surfaces, in Lean 4

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

## Layout

| file | contents |
|---|---|
| `Challenge.lean` | the structure, the definitions, and the four claimed statements (with `sorry`) |
| `Solution.lean` | the same statements, proved |
| `Audit.lean` | `#print axioms` for every claimed theorem |
| `comparator.json` | the four theorem names compared by [Comparator](https://github.com/leanprover/comparator) |
| `scripts/audit.sh` | the five trust conditions, fails closed |
| `scripts/mutation_test.py` | checks that every hypothesis is load-bearing |

## Building

```sh
lake exe cache get
lake build Challenge Solution Audit
./scripts/audit.sh
```

Lean `v4.31.0`, Mathlib pinned in `lake-manifest.json`.

## What the audit checks

1. `Challenge.olean` and `Solution.olean` are produced.
2. Every claimed theorem depends on exactly `propext`, `Classical.choice`,
   `Quot.sound` — no others.
3. No `sorry`, `native_decide`, `unsafe` or project-defined `axiom` in
   `Solution.lean`; exactly four deliberate `sorry` holes in `Challenge.lean`.
4. The four claimed theorems appear in both modules.
5. **Mutation test**: eleven single-token changes to the structure's fields and
   to the constants in the claimed statements each break the build, and two
   harmless edits do not.

Point 5 is there because a correct proof of a badly stated theorem still passes
points 1–4.  An earlier version of this development assumed `3·#F = 2·#E` as a
field of the structure; the mutation test then showed that "every face has three
vertices" was used by no proof at all.  The structure was reworked so that the
relation is derived and every field is load-bearing.

## Scope and limitations

The angles are abstract real data constrained only by summing to `π` on each
face.  Nothing embeds the surface in Euclidean space or derives the angles from
edge lengths, and the angles are not required to be positive.  `euler` is
defined as `#V − #E + #F` from the data and is not connected to any topological
invariant here.  Orientability and connectedness are neither assumed nor needed.

Full metadata, sources and limitations: `formalization.yaml`.
