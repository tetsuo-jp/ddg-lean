import Mathlib

/-!
# Discrete Gauss–Bonnet for closed triangulated surfaces (statement)

The total angle defect of a closed triangulated surface equals `2 * π * χ`.

The relation `3 * #F = 2 * #E` is **not** assumed: it is claimed as
`three_mul_card_faces`, and derived in the solution by double counting from
"every face has three vertices" and "every edge lies in exactly two faces".

The angles here are abstract real data constrained only by "the angles of a
face sum to `π`".  Nothing embeds the surface in Euclidean space or derives the
angles from a metric; this is the combinatorial form of the theorem.
-/

open Finset Real

variable {V F : Type} [Fintype V] [DecidableEq V] [Fintype F]

/-- A closed triangulated surface with angle data.  Faces are triangles, the
edges are the two-element vertex sets occurring in faces, and closedness is the
requirement that each edge lies in exactly two faces. -/
structure ClosedTriangulation (V F : Type) [Fintype V] [DecidableEq V] [Fintype F] where
  /-- the vertices of a face -/
  verts : F → Finset V
  /-- every face is a triangle -/
  card_verts : ∀ f, (verts f).card = 3
  /-- the interior angle of face `f` at vertex `v` -/
  angle : F → V → ℝ
  /-- the angles of a triangle sum to `π` -/
  angle_sum : ∀ f, ∑ v ∈ verts f, angle f v = π
  /-- a face contributes no angle at a vertex it does not contain -/
  angle_eq_zero : ∀ f v, v ∉ verts f → angle f v = 0
  /-- the edges -/
  edgeSet : Finset (Finset V)
  /-- an edge is exactly a two-element vertex set occurring in some face -/
  mem_edgeSet : ∀ e, e ∈ edgeSet ↔ (e.card = 2 ∧ ∃ f, e ⊆ verts f)
  /-- closedness: every edge lies in exactly two faces -/
  two_faces : ∀ e ∈ edgeSet, #{f | e ⊆ verts f} = 2

namespace ClosedTriangulation

variable (T : ClosedTriangulation V F)

/-- The angle defect at a vertex: `2 * π` minus the angles meeting there. -/
noncomputable def defect (v : V) : ℝ :=
  2 * π - ∑ f, T.angle f v

/-- The Euler characteristic `#V - #E + #F`. -/
def euler : ℤ :=
  (Fintype.card V : ℤ) - (T.edgeSet.card : ℤ) + (Fintype.card F : ℤ)

/-- **Every edge lies in two faces, every face has three edges.**  Hence
`3 * #F = 2 * #E`. -/
theorem three_mul_card_faces : 3 * Fintype.card F = 2 * T.edgeSet.card :=
  sorry

/-- **Discrete Gauss–Bonnet.** The total angle defect of a closed triangulated
surface is `2 * π` times its Euler characteristic. -/
theorem sum_defect_eq_two_pi_mul_euler :
    ∑ v, T.defect v = 2 * π * (T.euler : ℝ) :=
  sorry

/-- **The tetrahedron has six edges**: four triangular faces force `#E = 6`. -/
theorem card_edges_tetrahedron (hF : Fintype.card F = 4) : T.edgeSet.card = 6 :=
  sorry

/-- **The tetrahedron.** Four vertices and four faces: the total angle defect
is `4 * π`. -/
theorem sum_defect_tetrahedron (hV : Fintype.card V = 4) (hF : Fintype.card F = 4) :
    ∑ v, T.defect v = 4 * π :=
  sorry

end ClosedTriangulation
