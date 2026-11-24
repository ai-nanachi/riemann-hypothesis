module

public import Mathlib.NumberTheory.NumberField.Completion.FinitePlace

@[expose] public section

open NumberField

namespace Bl.general_b_fact_left_extra

variable {K : Type*} [Field K] [NumberField K]

theorem goal1 {ι : Type*} (w : FinitePlace K) (t : Finset ι) (a : ι → K) {M : ℝ}
    (hM : 0 ≤ M) (h : ∀ i ∈ t, w (a i) ≤ M) : w (∑ i ∈ t, a i) ≤ M := by
  rcases t.eq_empty_or_nonempty with rfl | ht
  · simpa using hM
  obtain ⟨i, hi, hle⟩ := (show IsNonarchimedean w from w.add_le).finset_image_add_of_nonempty a ht
  exact hle.trans (h i hi)

end Bl.general_b_fact_left_extra
