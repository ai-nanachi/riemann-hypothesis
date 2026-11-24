module

public import Mathlib.Algebra.Module.Lattice.Full
public import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Localization.Submodule

@[expose] public section

namespace Bl.general_b_fact_third_version

open NumberField in
theorem goal1 {E : Type} [Field E] [NumberField E] {V : Type} [AddCommGroup V]
    [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (Λ : Submodule (𝓞 E) V) (hΛ : Submodule.IsFullLattice E Λ) (v : V) :
    ∃ m : ℕ, m ≠ 0 ∧ (m : E) • v ∈ Λ := by
  let S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)
  let : IsLocalization S E := IsIntegralClosure.isLocalization ℤ ℚ E (𝓞 E)
  have hv : v ∈ Submodule.span E (Λ : Set V) := by simp [hΛ.span_eq_top]
  obtain ⟨w, hw, s, hvs⟩ :=
    (IsLocalization.mem_span_iff (R := 𝓞 E) (M := S) (S := E)).mp hv
  rw [Submodule.span_eq] at hw
  have hsv : (s : 𝓞 E) • v ∈ Λ := by
    rw [hvs, ← IsScalarTower.algebraMap_smul E (s : 𝓞 E), smul_smul,
      IsLocalization.mk'_spec', map_one, one_smul]
    exact hw
  obtain ⟨z, hz, hez⟩ := s.property
  have hzv : z • v ∈ Λ := by rwa [← algebraMap_smul (𝓞 E) z v, hez]
  have hz0 := nonZeroDivisors.ne_zero hz
  obtain ⟨n, rfl | rfl⟩ := z.eq_nat_or_neg
  · exact ⟨n, Int.natCast_ne_zero.mp hz0, by
      simpa only [natCast_zsmul, Nat.cast_smul_eq_nsmul] using hzv⟩
  · exact ⟨n, Int.natCast_ne_zero.mp (neg_ne_zero.mp hz0), by
      simpa only [neg_smul, neg_neg, natCast_zsmul, Nat.cast_smul_eq_nsmul] using Λ.neg_mem hzv⟩

end Bl.general_b_fact_third_version
