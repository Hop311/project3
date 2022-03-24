
import analysis.normed.normed_field

/-- A nonarchimedean field is a field with a norm satisfying ∥x + y∥ ≤ max ∥x∥ ∥y∥. -/
class nonarchimedean_field (𝕜) extends normed_field 𝕜 :=
(non_arch : ∀ x y : 𝕜, ∥x + y∥ ≤ max (∥x∥) (∥y∥))

section disc
  variables (𝕜 : Type) [normed_field 𝕜]

  def disc : Type := {x : 𝕜 // ∥x∥ ≤ 1}

  instance disc_normed_field : normed_field (disc 𝕜) := sorry
  
  instance disc_nonarchimedean_field [nonarchimedean_field 𝕜] : nonarchimedean_field (disc 𝕜) := sorry

  instance disc_complete [complete_space 𝕜] : complete_space (disc 𝕜) := sorry

end disc

variables {𝕜 : Type} [nonarchimedean_field 𝕜] [complete_space 𝕜]

variables (f : polynomial (disc 𝕜)) (t₀ : disc 𝕜) (ht₀ : ∥f.eval t₀∥ < ∥f.derivative.eval t₀∥ ^ 2)

theorem hensels_lemma : ∃ t, f.eval t = 0 ∧ ∥t - t₀∥ < ∥f.derivative.eval t₀∥ ∧
  ∥f.derivative.eval t∥ = ∥f.derivative.eval t₀∥ ∧ ∥t - t₀∥ = ∥f.eval t₀∥ / ∥f.derivative.eval t₀∥ ∧
  ∀ t', f.eval t' = 0 → ∥t' - t₀∥ < ∥f.derivative.eval t₀∥ → t' = t :=
begin
  sorry
end
