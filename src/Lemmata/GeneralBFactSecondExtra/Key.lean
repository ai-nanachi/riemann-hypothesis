module

public import Mathlib.RingTheory.Length

@[expose] public section

universe u_1 u_2

namespace Bl.general_b_fact_second'''

theorem goal1 {O : Type u_1} {Y : Type u_2} [CommRing O] [AddCommGroup Y] [Module O Y]
    (R S D E : Submodule O Y) (hD : ∀ y, y ∈ D ↔ y ∈ R ∧ y ∈ S) (hE : E ≤ D) :
    Module.length O (R ⧸ E.comap R.subtype) =
      Module.length O (R ⧸ S.comap R.subtype) + Module.length O (D ⧸ E.comap D.subtype) := by
  have hDR : D ≤ R := fun y hy => ((hD y).1 hy).1
  have hf : (E.comap R.subtype).comap (Submodule.inclusion hDR) = E.comap D.subtype := by
    rw [← Submodule.comap_comp, Submodule.subtype_comp_inclusion]
  have hg : E.comap R.subtype ≤ S.comap R.subtype :=
    Submodule.comap_mono fun y hy => ((hD y).1 (hE hy)).2
  let f := Submodule.mapQ (E.comap D.subtype) (E.comap R.subtype) (Submodule.inclusion hDR)
    (le_of_eq hf.symm)
  rw [add_comm]
  refine Module.length_eq_add_of_exact f (Submodule.factor hg) ?_ (Submodule.factor_surjective hg) ?_
  · dsimp only [f]
    rw [← LinearMap.ker_eq_bot, Submodule.ker_mapQ, hf, Submodule.mkQ_map_self]
  · dsimp only [f, Submodule.factor]
    rw [LinearMap.exact_iff, Submodule.ker_mapQ, Submodule.range_mapQ,
      Submodule.comap_id, Submodule.range_inclusion]
    congr 1
    ext x
    exact ⟨fun hx => (hD x).2 ⟨x.2, hx⟩, fun hx => ((hD x).1 hx).2⟩

end Bl.general_b_fact_second'''
