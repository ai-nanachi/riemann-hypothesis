module

public import Mathlib.RingTheory.Length
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Module.LocalizedModule.Exact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.ArakelovGeometry

variable {R : Type*} [CommRing R]

theorem length_loc_add {M₀ M₁ M₂ : Type*} [AddCommGroup M₀] [AddCommGroup M₁] [AddCommGroup M₂]
    [Module R M₀] [Module R M₁] [Module R M₂] (g : M₀ →ₗ[R] M₁) (h : M₁ →ₗ[R] M₂)
    (hg : Function.Injective g) (hh : Function.Surjective h) (ex : Function.Exact g h)
    (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₁) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₀) +
        Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl M₂) := by
  exact Module.length_eq_add_of_exact _ _ (LocalizedModule.map_injective _ g hg)
    (LocalizedModule.map_surjective _ h hh) (LocalizedModule.map_exact _ g h ex)

theorem length_loc_step (I q : Ideal R) (f : R) (hq : ∀ g, g ∈ q ↔ g * f ∈ I) (P : Ideal R)
    [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ I)) =
      Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) +
        Module.length (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (R ⧸ (I ⊔ Ideal.span {f}))) := by
  let g : (R ⧸ q) →ₗ[R] (R ⧸ I) :=
    Submodule.mapQ q I (LinearMap.mulRight R f) (by intro x hx; exact (hq x).mp hx)
  let π : (R ⧸ I) →ₗ[R] (R ⧸ (I ⊔ Ideal.span {f})) :=
    Submodule.mapQ I (I ⊔ Ideal.span {f}) LinearMap.id (by intro x hx; exact Ideal.mem_sup_left hx)
  have hg : Function.Injective g := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    change Submodule.Quotient.mk (p := I) (x * f) = 0 at hz
    rw [Submodule.Quotient.mk_eq_zero] at hz
    change Submodule.Quotient.mk (p := q) x = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact (hq x).mpr hz
  have hπ : Function.Surjective π := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk x, rfl⟩
  have hex : Function.Exact g π := by
    intro y
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    change Submodule.Quotient.mk (p := I ⊔ Ideal.span {f}) y = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · intro hy
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
      obtain ⟨r, rfl⟩ := Ideal.mem_span_singleton'.mp hb
      refine ⟨Submodule.Quotient.mk r, ?_⟩
      change Submodule.Quotient.mk (p := I) (r * f) = Submodule.Quotient.mk (a + r * f)
      rw [Submodule.Quotient.eq]
      simpa using I.neg_mem ha
    · rintro ⟨x, hx⟩
      obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      change Submodule.Quotient.mk (p := I) (x * f) = Submodule.Quotient.mk y at hx
      rw [Submodule.Quotient.eq] at hx
      have e : y = x * f - (x * f - y) := by ring
      rw [e]
      exact Submodule.sub_mem _ (Ideal.mem_sup_right (Ideal.mem_span_singleton'.mpr ⟨x, rfl⟩))
        (Ideal.mem_sup_left hx)
  exact length_loc_add g π hg hπ hex P

theorem length_loc_quot_eq_zero (q P : Ideal R) [P.IsPrime] (h : ¬ q ≤ P) :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ q)) = 0 := by
  obtain ⟨s, hsq, hsP⟩ := IsConcreteLE.not_le_iff_exists.mp h
  rw [Module.length_eq_zero_iff, LocalizedModule.subsingleton_iff]
  intro x
  refine ⟨s, hsP, ?_⟩
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
  exact q.mul_mem_right _ hsq

theorem length_loc_quot_self (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ P)) = 1 := by
  let S := Localization.AtPrime P
  let g := Submodule.toLocalizedQuotient' S P.primeCompl (Algebra.linearMap R S) P
  let e := (IsLocalizedModule.linearEquiv P.primeCompl g
    (LocalizedModule.mkLinearMap P.primeCompl (R ⧸ P))).restrictScalars S
  have h : Submodule.localized' S P.primeCompl (Algebra.linearMap R S) P = IsLocalRing.maximalIdeal S :=
    (Ideal.localized'_eq_map S P.primeCompl P).trans Localization.AtPrime.map_eq_maximalIdeal
  rw [← e.length_eq, (Submodule.quotEquivOfEq _ _ h).length_eq,
    Module.length_eq_one_iff, isSimpleModule_iff_isCoatom]
  exact Ideal.isMaximal_def.mp (IsLocalRing.maximalIdeal.isMaximal S)

theorem length_loc_top (P : Ideal R) [P.IsPrime] :
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ (⊤ : Ideal R))) = 0 := by
  apply length_loc_quot_eq_zero
  intro h
  exact ‹P.IsPrime›.ne_top (top_le_iff.mp h)

theorem length_loc_chain (P : Ideal R) [P.IsPrime] : ∀ (N : ℕ) (F : Fin (N + 1) → Ideal R)
    (f : Fin N → R) (q : Fin N → Ideal R), F (Fin.last N) = ⊤ →
    (∀ j : Fin N, F j.succ = F j.castSucc ⊔ Ideal.span {f j} ∧ (q j).IsPrime ∧
      ∀ g, g ∈ q j ↔ g * f j ∈ F j.castSucc) →
    (∀ j, q j ≤ P → q j = P) →
    Module.length (Localization.AtPrime P) (LocalizedModule P.primeCompl (R ⧸ F 0)) =
      ((∑ j : Fin N, if q j = P then 1 else 0 : ℕ) : ℕ∞) := by
  intro N
  induction N with
  | zero =>
    intro F f q hlast _ _
    rw [show F 0 = F (Fin.last 0) from rfl, hlast, length_loc_top]
    simp
  | succ N ih =>
    intro F f q hlast hj hmin
    have htail := ih (fun j => F j.succ) (fun j => f j.succ) (fun j => q j.succ)
      (by simpa only [Fin.succ_last] using hlast)
      (fun j => by simpa only [Fin.castSucc_succ] using hj j.succ)
      (fun j => hmin j.succ)
    obtain ⟨h1, _, h3⟩ := hj 0
    rw [Fin.castSucc_zero] at h1 h3
    rw [length_loc_step (F 0) (q 0) (f 0) h3 P, ← h1, htail, Fin.sum_univ_succ]
    by_cases hq : q 0 = P
    · rw [ite_eq_left hq, hq, length_loc_quot_self]
      push_cast
      ring
    · rw [ite_eq_right hq, length_loc_quot_eq_zero _ _ (fun h => hq (hmin 0 h))]
      simp

end ReciprocityTheory.ChartRestriction.G.ArakelovGeometry
