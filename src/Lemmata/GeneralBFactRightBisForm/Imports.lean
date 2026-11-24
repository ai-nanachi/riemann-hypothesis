module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.Module.Submodule.Map
public import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Multilinear.Basic

@[expose] public section

universe u_1 u_2 u_3 u_4

namespace Bl.general_b_fact_right_bis_form

theorem goal1 {R : Type u_1} [CommRing R] {ι : Type u_2} [Fintype ι] [DecidableEq ι]
    {M : ι → Type u_3} [(i : ι) → AddCommGroup (M i)] [(i : ι) → Module R (M i)]
    {A : Type u_4} [CommRing A] [Algebra R A]
    (φ : (i : ι) → M i →ₗ[R] A) (S : (i : ι) → Set (M i)) (T : Submodule R A)
    (hS : ∀ s : (i : ι) → M i, (∀ i, s i ∈ S i) → (∏ i, φ i (s i)) ∈ T)
    (m : (i : ι) → M i) (hm : ∀ i, m i ∈ Submodule.span R (S i)) :
    (∏ i, φ i (m i)) ∈ T := by
  classical
  let F : (∀ i, M i) →ₘₗ[R] A := (MultilinearMap.mkPiAlgebra R ι A).compLinearMap φ
  change F m ∈ T
  choose coeff supports hsubset _hcoeff hsum using
    fun i => (Submodule.mem_span_iff_exists_finset_subset.mp (hm i))
  have heq : m = fun i => ∑ x ∈ supports i, coeff i x • x :=
    funext fun i => (hsum i).symm
  rw [heq, F.map_sum_finset]
  refine T.sum_mem fun x hx => ?_
  rw [F.map_smul_univ]
  exact T.smul_mem _ (hS x fun i => hsubset i (Fintype.mem_piFinset.mp hx i))

end Bl.general_b_fact_right_bis_form
