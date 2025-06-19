import Mathlib.Algebra.Ring.Defs
import Mathlib.RingTheory.Jacobson.Radical
import Mathlib.RingTheory.Jacobson.Ideal
import Mathlib.RingTheory.Nilpotent.Defs
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.Ideal.Span
import Mathlib.Logic.Nontrivial.Defs

open Ring Ideal

variable {R}
variable [CommRing R]
variable {n: ℕ}
variable [NeZero n]

-- a is a unit iff a does not belong to any maximal ideal
lemma unit_iff_not_in_max
{a: R}:
IsUnit a ↔ ∀ I : Ideal R, IsMaximal I → ¬ a ∈ I := by
constructor
·
  intro h_au
  by_contra no_max
  rw[not_forall] at no_max
  simp at no_max
  obtain ⟨ M, M_max, aM ⟩ := no_max
  obtain ⟨ ia, h_ia ⟩ := h_au.exists_left_inv
  have abs : 1 ∈ M := by
    rw[← h_ia]
    exact mul_mem_left M ia aM
  -- 1 not in max
  have not := (isMaximal_iff.mp M_max).1
  tauto
·
-- a does not divide 1
-- a's generated ideal isn't r
-- a is contained in a maximal ideal
  intro h_nmax
  by_contra h_ninv

  let gen_a := span {a}
  have gen_a_not_top := span_singleton_ne_top h_ninv
  obtain ⟨ mx, mx_Max, gen_a_le_mx ⟩ := exists_le_maximal gen_a gen_a_not_top
  have a_mx : a ∈ mx := (span_singleton_le_iff_mem mx).mp gen_a_le_mx
  tauto

theorem ab_one_iff_jac
{a: R}:
(∀ b : R, IsUnit (1 + a*b)) ↔ a ∈ jacobson R := by
rw[jacobson_eq_sInf_isMaximal]
rw[mem_sInf]
constructor
·
  intro ab_inv
  simp
  intro I
  intro I_max
  by_contra a_I
  obtain ⟨ x, y, y_I , eq_inv ⟩ := IsMaximal.exists_inv I_max a_I
  have ax_minus_one := ab_inv (-x)
  rw[mul_comm] at ax_minus_one
  simp at ax_minus_one
  rw[add_comm, ←eq_sub_iff_add_eq] at eq_inv
  rw[eq_inv] at y_I
  rw[unit_iff_not_in_max] at ax_minus_one
  have contr := @ax_minus_one I I_max
  rw[← sub_eq_add_neg] at contr
  tauto
·
  intro a_in_max
  simp at a_in_max
  intro b
  rw[unit_iff_not_in_max]
  intro I
  intro I_max
  have a_in_I := (@a_in_max I) I_max
  by_contra one_ab_I
  have ab_I : a*b ∈ I := Ideal.mul_mem_right b I a_in_I
  have one_I := sub_mem one_ab_I ab_I
  simp at one_I
  exact (isMaximal_iff.mp I_max).1 one_I
