
import analysis.normed.normed_field
import data.polynomial.taylor

/-- A nonarchimedean type is a type with an addition operation and a norm satisfying ∥x + y∥ ≤ max ∥x∥ ∥y∥. -/
class nonarchimedean (𝕜) [has_add 𝕜] [has_norm 𝕜] :=
(nonarch : ∀ x y : 𝕜, ∥x + y∥ ≤ max (∥x∥) (∥y∥))

/-- A ℕ-indexed sequence in a nonarchimedian normed ring is Cauchy iff the difference
  of its consecutive terms tends to 0. -/
theorem nonarchimedean.cau {𝕜} [normed_ring 𝕜] [nonarchimedean 𝕜] (s : ℕ → 𝕜) :
  is_cau_seq norm s ↔ ∀ ε > 0, ∃ i, ∀ j ≥ i, ∥s (j + 1) - s j∥ < ε :=
begin
  apply forall₂_congr, intros ε hε,
  split,
  { rintro ⟨i, hi⟩, use i, intros j hj,
    exact sub_add_sub_cancel (s (j + 1)) (s i) (s j) ▸ neg_sub (s j) (s i) ▸
      lt_of_le_of_lt (nonarchimedean.nonarch (s (j + 1) - s i) (-(s j - s i)))
      (max_lt (hi (j + 1) (le_add_right hj)) ((norm_neg (s j - s i)).symm ▸ hi j hj)) },
  { rintro ⟨i, hi⟩, use i, intros j hj,
    cases le_iff_exists_add.mp hj with k hk,
    induction k with k ih generalizing j,
    { rw [(add_zero i ▸ hk : j = i), sub_self, norm_zero], exact hε },
    { exact hk.symm ▸ (sub_add_sub_cancel (s (i + k + 1)) (s (i + k)) (s i)) ▸
        lt_of_le_of_lt (nonarchimedean.nonarch (s (i + k + 1) - s (i + k)) (s (i + k) - s i))
        (max_lt (hi (i + k) le_self_add) (ih (i + k) le_self_add rfl)) } }
end

section disc
  variables (𝕜 : Type) [normed_ring 𝕜] [norm_one_class 𝕜] [nonarchimedean 𝕜]

  def disc : subring 𝕜 := {
    carrier   := {x | ∥x∥ ≤ 1},
    mul_mem'  := λ x y hx hy, (norm_mul_le x y).trans (one_mul (1 : ℝ) ▸
      mul_le_mul hx hy (norm_nonneg y) zero_le_one),
    one_mem'  := norm_one.le,
    add_mem'  := λ x y hx hy, (nonarchimedean.nonarch x y).trans (max_le hx hy),
    zero_mem' := norm_zero.le.trans zero_le_one,
    neg_mem'  := λ x hx, ((norm_neg x).symm ▸ hx : ∥-x∥ ≤ 1)
  }

  instance has_norm_disc : has_norm (disc 𝕜) := ⟨norm ∘ subtype.val⟩
  
  section
    variable {𝕜}
    theorem disc_norm (x : disc 𝕜) : ∥x∥ = ∥x.val∥ := rfl
  end

  instance disc_nonarchimedean : nonarchimedean (disc 𝕜) :=
    ⟨λ x y, (disc_norm (x + y)).symm ▸ nonarchimedean.nonarch x.val y.val⟩

  instance disc_complete [complete_space 𝕜] : complete_space (disc 𝕜) := {
    complete :=
    begin
      sorry
    end
  }

end disc

section taylor
  open polynomial
  variables {R : Type} [comm_ring R]

  theorem sum_term (n : ℕ) (f : polynomial R) (fn : ℕ → R → polynomial R) (h : ∀ k, fn k 0 = 0) :
    f.sum fn = fn n (f.coeff n) + (f.erase n).sum fn :=
  begin
    rw [sum_def, sum_def, support_erase],
    by_cases hn : n ∈ f.support,
    { rw [←finset.add_sum_erase f.support (λ n, fn n (f.coeff n)) hn],
      apply congr_arg, apply finset.sum_congr rfl, intros x hx,
      rw [erase_ne f n x (finset.ne_of_mem_erase hx)] },
    { rw [not_mem_support_iff.mp hn, h n, zero_add],
      exact eq.symm (finset.sum_congr (finset.erase_eq_of_not_mem hn)
        (λ x hx, congr_arg _ (erase_ne f n x (λ h, absurd (h ▸ hx : n ∈ f.support) hn)))) }
  end

  theorem polynomial.mul_sum {S} [ring S] (s : S) (f : polynomial R) (fn : ℕ → R → S) :
    s * f.sum fn = f.sum (λ i a, s * fn i a) := by rw [sum_def, sum_def, finset.mul_sum]

  theorem taylor (f : polynomial R) (t₀ : R) : ∃ err : polynomial R, ∀ t,
    f.eval t = f.eval t₀ + (t - t₀) * f.derivative.eval t₀ + (t - t₀)^2 * err.eval t :=
  begin
    use (((taylor t₀ f).erase 0).erase 1).sum (λ i a, C a * (X - C t₀) ^ (i - 2)), intro t,
    have : ∀ n, C 0 * (X - C t₀) ^ n = 0, { intro n, rw [C_0, zero_mul] },
    conv_lhs { rw [←f.sum_taylor_eq t₀, sum_term 0 (taylor t₀ f) (λ i a, C a * (X - C t₀) ^ i) this,
      sum_term 1 ((taylor t₀ f).erase 0) (λ i a, C a * (X - C t₀) ^ i) this, taylor_coeff_zero,
      erase_ne (taylor t₀ f) 0 1 nat.one_ne_zero, taylor_coeff_one], simp only,
      rw [pow_zero, mul_one, pow_one, ←add_assoc, mul_comm, eval_add, eval_add,
        eval_C, eval_mul, eval_sub, eval_X, eval_C, eval_C] },
    apply congr_arg,
    have : (t - t₀)^2 = ((X - C t₀) ^ 2).eval t := by rw [eval_pow, eval_sub, eval_X, eval_C],
    rw [this, ←eval_mul], apply congr_arg,
    rw [sum_def, sum_def, finset.mul_sum, finset.sum_congr rfl],
    intros n hn,
    conv_rhs { rw [mul_comm, mul_assoc, ←pow_add], },
    have : 2 ≤ n,
    { cases n with n,
      { exfalso, rw [support_erase, support_erase, finset.erase_right_comm] at hn,
        exact absurd rfl (finset.ne_of_mem_erase hn) },
      { cases n with n, { rw [support_erase] at hn, exact absurd rfl (finset.ne_of_mem_erase hn) },
        { simp only [succ_order.succ_le_succ_iff, zero_le'] } } },
    rw [nat.sub_add_cancel this]
  end
end taylor

variables {𝕜 : Type} [normed_field 𝕜] [nonarchimedean 𝕜] [complete_space 𝕜]

variables (f : polynomial (disc 𝕜)) (t₀ : disc 𝕜) (ht₀ : ∥f.eval t₀∥ < ∥f.derivative.eval t₀∥ ^ 2)

theorem hensels_lemma : ∃ t, f.eval t = 0 ∧ ∥t - t₀∥ < ∥f.derivative.eval t₀∥ ∧
  ∥f.derivative.eval t∥ = ∥f.derivative.eval t₀∥ ∧ ∥t - t₀∥ = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥ ∧
  ∀ t', f.eval t' = 0 → ∥t' - t₀∥ < ∥f.derivative.eval t₀∥ → t' = t :=
begin
  sorry
end
