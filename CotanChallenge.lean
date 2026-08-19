import Mathlib

/-!
# The cotangent formula for the Dirichlet energy of a triangle (statement)

For a triangle in the Euclidean plane and an affine function on it, the
Dirichlet energy `A * ‖∇u‖ ^ 2` equals `(1/2) * ∑ₖ cot θₖ * (uᵢ - uⱼ) ^ 2`, the
sum running over the three vertices, `θₖ` the interior angle at vertex `k` and
`uᵢ - uⱼ` the jump of `u` across the edge opposite `k`.  This is the identity
behind the cotangent Laplacian.

The gradient is characterised without calculus: `g` is the gradient of the
affine interpolant exactly when `⟪g, pᵢ - pⱼ⟫ = uᵢ - uⱼ` along edges, so the
statements below read the edge differences off `⟪g, eₖ⟫`.

`inner_form` states the identity with `cot θₖ * 2A` replaced by an inner product
of edges; it needs no hypotheses at all.  `cotan_form` is the cotangent version
and needs the triangle to be nondegenerate.

-/

open Real InnerProductGeometry

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

namespace Cotan

/-- The scalar cross product of two vectors of the plane. -/
def cross (a b : E2) : ℝ := a 0 * b 1 - a 1 * b 0

/-- **The Gram matrix of three plane vectors is singular.**  This is the whole
geometric content of the cotangent formula. -/
theorem gram_two (g u v : E2) :
    ‖u‖ ^ 2 * inner ℝ g v ^ 2 - 2 * inner ℝ u v * inner ℝ g u * inner ℝ g v
      + ‖v‖ ^ 2 * inner ℝ g u ^ 2 = cross u v ^ 2 * ‖g‖ ^ 2 :=
  sorry

variable (p : Fin 3 → E2)

/-- The edge opposite vertex `0`. -/
def e0 : E2 := p 2 - p 1
/-- The edge opposite vertex `1`. -/
def e1 : E2 := p 0 - p 2
/-- The edge opposite vertex `2`. -/
def e2 : E2 := p 1 - p 0

/-- Twice the signed area of the triangle `p 0, p 1, p 2`. -/
def sarea2 : ℝ :=
  (p 1 0 - p 0 0) * (p 2 1 - p 0 1) - (p 2 0 - p 0 0) * (p 1 1 - p 0 1)

/-- **The cotangent identity, before cotangents appear.**  For every `g` the
inner products of the edge pairs meeting at the three vertices reproduce
`(2A) ^ 2 * ‖g‖ ^ 2`.  No nondegeneracy is needed. -/
theorem inner_form (g : E2) :
    - inner ℝ (e1 p) (e2 p) * inner ℝ g (e0 p) ^ 2
    - inner ℝ (e0 p) (e2 p) * inner ℝ g (e1 p) ^ 2
    - inner ℝ (e0 p) (e1 p) * inner ℝ g (e2 p) ^ 2
      = sarea2 p ^ 2 * ‖g‖ ^ 2 :=
  sorry

/-- `cot` of the angle between two plane vectors, scaled by twice the area of the
triangle they span, is their inner product. -/
theorem cot_angle_mul_abs_cross (x y : E2) (h : cross x y ≠ 0) :
    Real.cot (angle x y) * |cross x y| = inner ℝ x y :=
  sorry

/-- The interior angle at vertex `0`. -/
noncomputable def angle0 : ℝ := angle (p 1 - p 0) (p 2 - p 0)
/-- The interior angle at vertex `1`. -/
noncomputable def angle1 : ℝ := angle (p 2 - p 1) (p 0 - p 1)
/-- The interior angle at vertex `2`. -/
noncomputable def angle2 : ℝ := angle (p 0 - p 2) (p 1 - p 2)

/-- **The cotangent formula.**  For a nondegenerate triangle and any `g`, the
cotangents of the three interior angles weight the squared edge differences of
`g` so as to give `2A * ‖g‖ ^ 2`.  Taking `g` to be the gradient of the affine
interpolant of vertex values `u`, this is the Dirichlet energy of `u` on the
triangle. -/
theorem cotan_form (hp : sarea2 p ≠ 0) (g : E2) :
    Real.cot (angle0 p) * inner ℝ g (e0 p) ^ 2
  + Real.cot (angle1 p) * inner ℝ g (e1 p) ^ 2
  + Real.cot (angle2 p) * inner ℝ g (e2 p) ^ 2
      = |sarea2 p| * ‖g‖ ^ 2 :=
  sorry

end Cotan
