module

public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Defs
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic

@[expose] public section

namespace Bl.FirstBlockLemmaG

/-- In a local ring, subtracting an element of the maximal ideal from a unit leaves a unit. -/
theorem goal1 {O : Type} [CommRing O] [IsLocalRing O] {a m : O}
    (ha : IsUnit a) (hm : m ∈ IsLocalRing.maximalIdeal O) : IsUnit (a - m) := by
  have hu : IsUnit ((a - m) + m) := by simpa only [sub_add_cancel] using ha
  exact (IsLocalRing.isUnit_or_isUnit_of_isUnit_add hu).resolve_right
    (mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal m).mp hm))

end Bl.FirstBlockLemmaG
