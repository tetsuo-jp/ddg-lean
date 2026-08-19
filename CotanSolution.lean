import Mathlib

/-!
# The cotangent formula for the Dirichlet energy of a triangle

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

The whole content is the degeneracy of the Gram matrix of three vectors in the
plane (`gram_two`).  Expanding that in coordinates and calling `ring` costs
minutes; keeping the inner products opaque and feeding `ring` only the Lagrange
and Binet–Cauchy identities costs seconds.
-/

open Real InnerProductGeometry

/-- The Euclidean plane. -/
abbrev E2 := EuclideanSpace ℝ (Fin 2)

namespace Cotan

/-- The scalar cross product of two vectors of the plane. -/
def cross (a b : E2) : ℝ := a 0 * b 1 - a 1 * b 0

@[simp] theorem cross_zero_left (b : E2) : cross 0 b = 0 := by simp [cross]

theorem inner_expand (a b : E2) : inner ℝ a b = a 0 * b 0 + a 1 * b 1 := by
  simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two]
  ring

theorem norm_sq_expand (a : E2) : ‖a‖ ^ 2 = a 0 ^ 2 + a 1 ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, inner_expand]; ring

/-- **Lagrange's identity** in the plane. -/
theorem lagrange (a b : E2) :
    ‖a‖ ^ 2 * ‖b‖ ^ 2 = inner ℝ a b ^ 2 + cross a b ^ 2 := by
  simp only [norm_sq_expand, inner_expand, cross]; ring

/-- **The Binet–Cauchy identity** in the plane. -/
theorem binet (g u v : E2) :
    ‖g‖ ^ 2 * inner ℝ u v = inner ℝ g u * inner ℝ g v + cross g u * cross g v := by
  simp only [norm_sq_expand, inner_expand, cross]; ring

/-- Resolving a plane vector against two others. -/
theorem cross_resolve (g u v : E2) :
    inner ℝ g u * cross g v - inner ℝ g v * cross g u = ‖g‖ ^ 2 * cross u v := by
  simp only [norm_sq_expand, inner_expand, cross]; ring

/-- **The Gram matrix of three plane vectors is singular.**  This is the whole
geometric content of the cotangent formula. -/
theorem gram_two (g u v : E2) :
    ‖u‖ ^ 2 * inner ℝ g v ^ 2 - 2 * inner ℝ u v * inner ℝ g u * inner ℝ g v
      + ‖v‖ ^ 2 * inner ℝ g u ^ 2 = cross u v ^ 2 * ‖g‖ ^ 2 := by
  rcases eq_or_ne g 0 with rfl | hg
  · simp
  · have hGG : ‖g‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hg)
    have h1 := lagrange g u
    have h2 := lagrange g v
    have h4 := binet g u v
    have h5 := cross_resolve g u v
    refine mul_left_cancel₀ hGG ?_
    linear_combination inner ℝ g v ^ 2 * h1 - 2 * inner ℝ g u * inner ℝ g v * h4
      + inner ℝ g u ^ 2 * h2
      + (inner ℝ g u * cross g v - inner ℝ g v * cross g u + ‖g‖ ^ 2 * cross u v) * h5

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

theorem sarea2_eq_cross : sarea2 p = cross (p 1 - p 0) (p 2 - p 0) := by
  simp only [sarea2, cross, PiLp.sub_apply]; ring

/-- **The cotangent identity, before cotangents appear.**  For every `g` the
inner products of the edge pairs meeting at the three vertices reproduce
`(2A) ^ 2 * ‖g‖ ^ 2`.  No nondegeneracy is needed. -/
theorem inner_form (g : E2) :
    - inner ℝ (e1 p) (e2 p) * inner ℝ g (e0 p) ^ 2
    - inner ℝ (e0 p) (e2 p) * inner ℝ g (e1 p) ^ 2
    - inner ℝ (e0 p) (e1 p) * inner ℝ g (e2 p) ^ 2
      = sarea2 p ^ 2 * ‖g‖ ^ 2 := by
  have h := gram_two g (p 1 - p 0) (p 2 - p 0)
  rw [sarea2_eq_cross]
  set u := p 1 - p 0 with hu
  set v := p 2 - p 0 with hv
  have he0 : e0 p = v - u := by rw [e0, hu, hv]; abel
  have he1 : e1 p = -v := by rw [e1, hv]; abel
  have he2 : e2 p = u := by rw [e2, hu]
  rw [he0, he1, he2]
  simp only [inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    real_inner_self_eq_norm_sq, real_inner_comm v u]
  linear_combination h - 2 * inner ℝ g u * inner ℝ g v * real_inner_comm u v

/-- `cot` of the angle between two plane vectors, scaled by twice the area of the
triangle they span, is their inner product. -/
theorem cot_angle_mul_abs_cross (x y : E2) (h : cross x y ≠ 0) :
    Real.cot (angle x y) * |cross x y| = inner ℝ x y := by
  have hs : Real.sin (angle x y) * (‖x‖ * ‖y‖) = |cross x y| := by
    rw [sin_angle_mul_norm_mul_norm]
    have hxy : inner ℝ x x * inner ℝ y y - inner ℝ x y * inner ℝ x y = cross x y ^ 2 := by
      rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
      linear_combination lagrange x y
    rw [hxy, Real.sqrt_sq_eq_abs]
  have hsne : Real.sin (angle x y) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at hs
    exact h (abs_eq_zero.mp hs.symm)
  rw [Real.cot_eq_cos_div_sin, ← hs]
  field_simp
  linear_combination cos_angle_mul_norm_mul_norm x y

/-- The interior angle at vertex `0`. -/
noncomputable def angle0 : ℝ := angle (p 1 - p 0) (p 2 - p 0)
/-- The interior angle at vertex `1`. -/
noncomputable def angle1 : ℝ := angle (p 2 - p 1) (p 0 - p 1)
/-- The interior angle at vertex `2`. -/
noncomputable def angle2 : ℝ := angle (p 0 - p 2) (p 1 - p 2)

theorem sarea2_eq_cross1 : sarea2 p = cross (p 2 - p 1) (p 0 - p 1) := by
  simp only [sarea2, cross, PiLp.sub_apply]; ring

theorem sarea2_eq_cross2 : sarea2 p = cross (p 0 - p 2) (p 1 - p 2) := by
  simp only [sarea2, cross, PiLp.sub_apply]; ring

/-- **The cotangent formula.**  For a nondegenerate triangle and any `g`, the
cotangents of the three interior angles weight the squared edge differences of
`g` so as to give `2A * ‖g‖ ^ 2`.  Taking `g` to be the gradient of the affine
interpolant of vertex values `u`, this is the Dirichlet energy of `u` on the
triangle. -/
theorem cotan_form (hp : sarea2 p ≠ 0) (g : E2) :
    Real.cot (angle0 p) * inner ℝ g (e0 p) ^ 2
  + Real.cot (angle1 p) * inner ℝ g (e1 p) ^ 2
  + Real.cot (angle2 p) * inner ℝ g (e2 p) ^ 2
      = |sarea2 p| * ‖g‖ ^ 2 := by
  have habs : |sarea2 p| ≠ 0 := abs_ne_zero.mpr hp
  have c0 : Real.cot (angle0 p) * |sarea2 p| = - inner ℝ (e1 p) (e2 p) := by
    rw [angle0, sarea2_eq_cross, cot_angle_mul_abs_cross _ _ (by rwa [← sarea2_eq_cross]),
      e1, e2]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm (p 1) (p 0),
      real_inner_comm (p 2) (p 0), real_inner_comm (p 2) (p 1)]
    ring
  have c1 : Real.cot (angle1 p) * |sarea2 p| = - inner ℝ (e0 p) (e2 p) := by
    rw [angle1, sarea2_eq_cross1, cot_angle_mul_abs_cross _ _ (by rwa [← sarea2_eq_cross1]),
      e0, e2]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm (p 1) (p 0),
      real_inner_comm (p 2) (p 0), real_inner_comm (p 2) (p 1)]
    ring
  have c2 : Real.cot (angle2 p) * |sarea2 p| = - inner ℝ (e0 p) (e1 p) := by
    rw [angle2, sarea2_eq_cross2, cot_angle_mul_abs_cross _ _ (by rwa [← sarea2_eq_cross2]),
      e0, e1]
    simp only [inner_sub_left, inner_sub_right, real_inner_comm (p 1) (p 0),
      real_inner_comm (p 2) (p 0), real_inner_comm (p 2) (p 1)]
    ring
  have h := inner_form p g
  rw [← sq_abs (sarea2 p)] at h
  refine mul_right_cancel₀ habs ?_
  linear_combination inner ℝ g (e0 p) ^ 2 * c0 + inner ℝ g (e1 p) ^ 2 * c1
    + inner ℝ g (e2 p) ^ 2 * c2 + h

end Cotan
