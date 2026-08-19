import Mathlib

/-!
# Discrete Gauss–Bonnet for closed triangulated surfaces

The total angle defect of a closed triangulated surface equals `2 * π * χ`.

The combinatorial content is small and worth isolating: once one knows that the
angles of a triangle sum to `π`, the rest is finite bookkeeping.  The relation
`3 * #F = 2 * #E` is **not** assumed here — it is derived, by double counting,
from "every face has three vertices" and "every edge lies in exactly two faces".
The tetrahedron (`χ = 2`, total defect `4 * π`) is the smallest instance.
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

/-- The edges contained in a fixed face are exactly the two-element subsets of
its vertex set, and there are three of them. -/
theorem card_edges_in_face (f : F) : #{e ∈ T.edgeSet | e ⊆ T.verts f} = 3 := by
  have h : {e ∈ T.edgeSet | e ⊆ T.verts f} = powersetCard 2 (T.verts f) := by
    ext e
    simp only [Finset.mem_filter, Finset.mem_powersetCard, T.mem_edgeSet]
    exact ⟨fun ⟨⟨hc, _⟩, hs⟩ => ⟨hs, hc⟩, fun ⟨hs, hc⟩ => ⟨⟨hc, ⟨f, hs⟩⟩, hs⟩⟩
  rw [h, Finset.card_powersetCard, T.card_verts f]
  rfl

/-- **Every edge lies in two faces, every face has three edges.**  Hence
`3 * #F = 2 * #E`.  This is where `card_verts` and `two_faces` are used. -/
theorem three_mul_card_faces : 3 * Fintype.card F = 2 * T.edgeSet.card := by
  have key : ∑ f : F, #{e ∈ T.edgeSet | e ⊆ T.verts f}
           = ∑ e ∈ T.edgeSet, #{f | e ⊆ T.verts f} := by
    simp only [Finset.card_filter]
    exact Finset.sum_comm
  rw [Finset.sum_congr rfl (fun f _ => T.card_edges_in_face f),
      Finset.sum_congr rfl (fun e he => T.two_faces e he)] at key
  simpa [Finset.card_univ, mul_comm] using key

/-- The angle defect at a vertex: `2 * π` minus the angles meeting there. -/
noncomputable def defect (v : V) : ℝ :=
  2 * π - ∑ f, T.angle f v

/-- The Euler characteristic `#V - #E + #F`. -/
def euler : ℤ :=
  (Fintype.card V : ℤ) - (T.edgeSet.card : ℤ) + (Fintype.card F : ℤ)

/-- The angles of a face, summed over *all* vertices, still sum to `π`. -/
theorem angle_sum_univ (f : F) : ∑ v, T.angle f v = π := by
  rw [← T.angle_sum f]
  exact (Finset.sum_subset (Finset.subset_univ _)
    (fun v _ hv => T.angle_eq_zero f v hv)).symm

/-- **Total defect, counted face-by-face.** -/
theorem sum_defect_eq_card :
    ∑ v, T.defect v = 2 * π * (Fintype.card V : ℝ) - π * (Fintype.card F : ℝ) := by
  have h : ∑ v, ∑ f, T.angle f v = π * (Fintype.card F : ℝ) := by
    rw [Finset.sum_comm]
    simp [T.angle_sum_univ, Finset.card_univ, mul_comm]
  simp only [defect, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, h]
  ring

/-- **Discrete Gauss–Bonnet.** The total angle defect of a closed triangulated
surface is `2 * π` times its Euler characteristic. -/
theorem sum_defect_eq_two_pi_mul_euler :
    ∑ v, T.defect v = 2 * π * (T.euler : ℝ) := by
  have hE : 2 * (T.edgeSet.card : ℝ) = 3 * (Fintype.card F : ℝ) := by
    exact_mod_cast T.three_mul_card_faces.symm
  rw [T.sum_defect_eq_card, euler]
  push_cast
  have hE' : (T.edgeSet.card : ℝ) = 3 / 2 * (Fintype.card F : ℝ) := by linarith
  rw [hE']
  ring

/-- **The tetrahedron.** Four vertices and four faces force six edges, and the
total angle defect is `4 * π`. -/
theorem card_edges_tetrahedron (hF : Fintype.card F = 4) : T.edgeSet.card = 6 := by
  have := T.three_mul_card_faces
  omega

theorem sum_defect_tetrahedron (hV : Fintype.card V = 4) (hF : Fintype.card F = 4) :
    ∑ v, T.defect v = 4 * π := by
  rw [T.sum_defect_eq_card, hV, hF]
  push_cast
  ring

end ClosedTriangulation
