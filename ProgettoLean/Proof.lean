import Mathlib.Algebra.Ring.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Defs
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Set.Basic
import Init.Data.Nat.Basic
import Init.Data.Nat.Dvd
import Init.Data.Int.Pow
import Mathlib.Tactic.Zify
import Mathlib.Data.Finsupp.Basic
import ProgettoLean.Ring_lemmas

open Nat

variable {N: ℕ}
variable [NeZero N]

def MyNilpotent(x: ZMod N) : Prop :=
  ∃ k : ℕ, k > 0 ∧ x ^ k = 0

-- this is indeed equivalent to the standard IsNilpotent
lemma myNil_eq_Nil
{x: ZMod N}:
MyNilpotent x ↔ IsNilpotent x := by
constructor
·
  intro h
  obtain ⟨ k, k_pos, xk ⟩ := h
  use k
·
  intro h
  obtain ⟨ k, xk ⟩ := h
  use k+1
  rw[pow_succ, xk]
  simp

-- we love mathlib --
lemma my_val_pow
{k: ℕ}
{x: ZMod N} :
x ^ k = ↑(x.val ^ k) := by
  induction k with
  | zero =>
    rw[pow_zero, pow_zero]
    simp
  | succ d hd =>
    rw[pow_succ, pow_succ]
    rw[hd]
    simp

-- a is nilpotent → m | a^k for some k
lemma nil_iff_div_pow
{x: ZMod N} :
MyNilpotent x ↔ ∃ k : ℕ, k > 0 ∧ N ∣ (x.val ^ k) := by
  constructor
  ·
    intro mp
    obtain ⟨k, k_pos, hk_zero⟩ := mp
    -- we can use the k given by nilpotency
    use k
    split_ands
    exact k_pos
    rw [my_val_pow] at hk_zero
    rw [ZMod.natCast_zmod_eq_zero_iff_dvd] at hk_zero
    exact hk_zero
  ·
    intro mpr
    obtain ⟨k, k_pos, hk_zero⟩ := mpr
    use k
    split_ands
    exact k_pos
    rw [← ZMod.natCast_zmod_eq_zero_iff_dvd] at hk_zero
    rw [← my_val_pow] at hk_zero
    exact hk_zero


-- a is nilpotent ↔ a has all of m's prime factors or a = 0
lemma nil_iff_same_primes_or_zero
{a: ZMod N} :
MyNilpotent a ↔ a = 0 ∨ (primeFactors N) ⊆ (primeFactors a.val) := by
  constructor
  ·
    intro hnil
    by_cases h: a = 0
    ·
      left
      exact h
    .
      right
      have hanz : a ≠ 0 := h
      obtain ⟨ k, k_pos, div_pow ⟩ := (nil_iff_div_pow).mp hnil
      -- a^k ≠ 0 (as int)
      rewrite[← ZMod.val_ne_zero] at hanz
      have a_pos := Nat.pos_of_ne_zero hanz
      have ak_pos : 0 < a.val ^ k := Nat.pow_pos a_pos
      have ak_nz : a.val ^ k ≠ 0 := (Nat.pos_iff_ne_zero).mp ak_pos

      rw[gt_iff_lt] at k_pos
      rw[Nat.pos_iff_ne_zero] at k_pos

      have p_cont := primeFactors_mono div_pow ak_nz
      rw[Nat.primeFactors_pow] at p_cont
      exact p_cont
      exact k_pos
  ·
    intro h
    cases h with
    | inl h =>
      -- a = 0
      use 1
      split_ands
      simp
      rw[h]
      simp
    | inr h =>
      by_cases az: a=0
      ·
        use 1
        split_ands
        tauto
        rw[az]
        simp
      ·
        -- a.val has m's prime factors
        have av_nz : a.val ≠ 0 :=
          (ZMod.val_ne_zero a).mpr az
        have av_pos : 0 < a.val :=
          Nat.pos_iff_ne_zero.mpr av_nz
        have am_nz : a.val ^ N ≠ 0 :=
          Nat.pos_iff_ne_zero.mp (Nat.pow_pos av_pos)

        rw[nil_iff_div_pow]
        let m_fact := N.factorization
        use N
        have nnz := NeZero.ne N
        split_ands
        exact Nat.pos_iff_ne_zero.mpr nnz
        rw[← factorization_prime_le_iff_dvd nnz am_nz]
        intro p
        intro p_prime
        by_cases pdiv: p ∈ N.primeFactors
        ·
          -- p is a factor of m
          -- we prove that m.factorization p ≤ m
          have f_lt_m := Nat.factorization_lt p nnz
          -- and that a.factorization p ≥ 1
          have p_in_af : p ∈ a.val.primeFactors := h pdiv
          have p_f_nz : 0 < a.val.factorization p := by
            have p_div := ((Nat.mem_primeFactors_of_ne_zero av_nz).mp p_in_af).2
            exact Nat.Prime.factorization_pos_of_dvd p_prime av_nz p_div

          have p_pow_ge_m : (a.val ^ N).factorization p ≥ N := by
            rw[Nat.factorization_pow (n:=a.val)]
            simp
            exact Nat.le_mul_of_pos_right N p_f_nz

          have f_le_m := Nat.le_of_lt f_lt_m
          exact le_trans f_le_m p_pow_ge_m

        ·
          -- p isn't a factor of m
          -- m.factorization p = 0 ≤ anything
          have pnd : ¬ p ∣ N := by
            by_contra!
            rw[mem_primeFactors_of_ne_zero nnz] at pdiv
            have aaa : Nat.Prime p ∧ p ∣ N := by
              split_ands
              exact p_prime
              exact this
            exact pdiv aaa

          have fact_zero : N.factorization p = 0 := by
            by_contra! mp
            exact pnd (Nat.dvd_of_factorization_pos mp)

          rw[fact_zero]
          simp

lemma plus_one_coprime_iff_same_primes_or_zero
{a: ZMod N} :
(∀ b : ZMod N, Coprime N (1 + a.val * b.val)) ↔ a = 0 ∨ (primeFactors N) ⊆ (primeFactors a.val) := by
  have nnz := NeZero.ne N
  constructor
  ·
    intro h_cop
    by_cases az: a = 0
    ·
      left
      tauto
    ·
      right
      intro p hp
      rw[Nat.mem_primeFactors]
      obtain ⟨ p_prime, p_div, nnz ⟩ := Nat.mem_primeFactors.mp hp
      split_ands
      tauto
      case neg.h.intro.intro.refine_2.refine_2 =>
        exact (ZMod.val_ne_zero a).mpr az

      -- if p does not divide a, then there exists
      -- b s.t. p | a*b + 1
      by_contra hpd

      have ap_gcd : p.gcd a.val = 1 := by
        rw[← Nat.coprime_iff_gcd_eq_one]
        rw[Nat.Prime.dvd_iff_not_coprime p_prime] at hpd
        tauto
      rw[gcd_rec] at ap_gcd

      have inv_a_mod_p : ∃ bb, (a.val * bb) % p = 1 := by
        let amp : ZMod p := a.val
        have prod_one := ZMod.mul_inv_eq_gcd amp
        have cast_stuff : amp.val = a.val % p := by
          rw[ZMod.val_natCast]

        rw[cast_stuff, ap_gcd] at prod_one
        use amp⁻¹.val
        rw[mul_mod, ← cast_stuff]
        simp
        rw[← ZMod.val_mul, prod_one]
        have p_gt_one : 1 < p := Nat.Prime.one_lt p_prime
        haveI : Fact (1 < p) := ⟨p_gt_one⟩
        simp
        exact ZMod.val_one p

      obtain ⟨ bb, bb_inv ⟩ := inv_a_mod_p

      have build_ce : (1 + a.val * bb * (p-1)) % p = 0 := by
        rw[add_mod]
        rw[mul_mod]
        rw[bb_inv]
        simp
        have p_ge_one : p ≥ 1 := le_of_lt (Nat.Prime.one_lt p_prime)
        rw [← Nat.add_sub_assoc p_ge_one]
        simp

      let b: ZMod N := (bb.cast * (p-1).cast)
      let x := 1 + a.val * b.val
      have hx_modp : (1 + a.val * b.val) % p = 0 := by
        subst b
        rw[add_mod]
        rw[mul_mod]
        simp
        rw[ZMod.val_mul]
        simp
        rw [← Nat.mod_mod_of_dvd (1 + a.val * (bb * (p - 1) % N)) p_div]
        rw[Nat.add_mod, Nat.mul_mod]
        simp

        rw [Nat.mod_mod_of_dvd (1 + a.val * (bb * (p - 1))) p_div]
        rw[← mul_assoc]
        exact build_ce

      have p_dvd_ab := dvd_iff_mod_eq_zero.mpr hx_modp

      -- we finally got our absurdity: m and 1 + a.val * b.val are not coprime!
      have nope : ¬N.Coprime (1 + a.val * b.val) := by
        rw[Nat.Prime.not_coprime_iff_dvd]
        use p

      tauto

  ·
    intro h
    intro b
    cases h with
    | inl h =>
      rw[h]
      simp
    | inr h =>
      rw [Nat.coprime_iff_gcd_eq_one]
      apply Nat.coprime_of_dvd
      intro p p_prime hpdm hpdab
      have ppm : p ∈ primeFactors N := by
        rw[mem_primeFactors]
        split_ands
        exact p_prime
        exact hpdm
        exact nnz

      have ppa : p ∈ primeFactors a.val := h ppm
      have p_div_a : p ∣ a.val := dvd_of_mem_primeFactors ppa

      have p_div_ab := Nat.dvd_mul_right_of_dvd p_div_a b.val
      have p_div_one : p ∣ 1 := by
        rw[← Nat.dvd_add_iff_left p_div_ab] at hpdab
        exact hpdab
      exact Nat.Prime.not_dvd_one p_prime p_div_one


theorem unit_iff_val_coprime
{a: ZMod N}:
IsUnit a ↔ a.val.Coprime N := by
rw[← ZMod.isUnit_iff_coprime]
rw[ZMod.natCast_val]
simp


lemma eq_mod_cop_iff
{x y n: ℕ}(heq: x % n = y % n):
n.Coprime x ↔ n.Coprime y := by
  rw [Nat.Coprime, Nat.Coprime]
  rw[Nat.gcd_rec]
  nth_rewrite 2 [Nat.gcd_rec]
  rw[heq]

theorem ex158
{a: ZMod N}:
MyNilpotent a ↔ ∀ b : ZMod N, IsUnit (1 + a*b) := by
  rw[nil_iff_same_primes_or_zero]
  rw[← plus_one_coprime_iff_same_primes_or_zero]
  constructor
  ·
    intro h
    intro b
    rw[unit_iff_val_coprime]
    have hb:= h b
    rw[coprime_comm]
    set x : ℕ := (1 + a.val * b.val) with hx
    set y : ℕ := (1 + a * b).val with hy
    -- have eq_zmod : ((1 + a.val * b.val) : ZMod m) = ((1 + a * b).val : ZMod m) := by
    --   simp
    have eq_mod_m : x % N = y % N := by
      rw[hx]
      rw[hy]
      rw[← ZMod.val_natCast]
      rw[← ZMod.val_natCast]
      simp

    rw[hx] at hb
    exact (eq_mod_cop_iff eq_mod_m).mp hb
  ·
    intro h
    intro b
    have hb:= h b
    rw[unit_iff_val_coprime] at hb
    set x : ℕ := (1 + a.val * b.val) with hx
    set y : ℕ := (1 + a * b).val with hy
    -- have eq_zmod : ((1 + a.val * b.val) : ZMod m) = ((1 + a * b).val : ZMod m) := by
    --   simp
    have eq_mod_m : x % N = y % N := by
      rw[hx]
      rw[hy]
      rw[← ZMod.val_natCast]
      rw[← ZMod.val_natCast]
      simp

    rw[coprime_comm] at hb

    exact (eq_mod_cop_iff eq_mod_m).mpr hb

theorem nil_iff_jac
{a: ZMod N}:
IsNilpotent a ↔ a ∈ Ring.jacobson (ZMod N) := by
  rw[← ab_one_iff_jac]
  rw[← myNil_eq_Nil]

  exact ex158
