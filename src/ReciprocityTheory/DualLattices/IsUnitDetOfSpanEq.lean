module

public import Mathlib.Basic.NNReal.Defs
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Valuation.Integers
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
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.Basify
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Lemma
import Mathlib.Tactic.Linter.Style
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

@[expose] public section

noncomputable section

open Matrix Finset

namespace ReciprocityTheory.PGsh.L2

variable {C : Type} [Field C] {R : Type} [CommRing R] [Algebra R C] {v : Valuation C NNReal}

theorem det_map_algebraMap {X : Type} [Fintype X] [DecidableEq X] (M : Matrix X X R) :
    (M.map (algebraMap R C)).det = algebraMap R C M.det := by
  exact (RingHom.map_det (algebraMap R C) M).symm

theorem eq_one_of_le_one_of_mul_eq_one {a b : NNReal} (ha : a ≤ 1) (hb : b ≤ 1) (h : a * b = 1) :
    a = 1 := by
  exact eq_one_of_one_le_mul_left ha hb h.ge

private lemma col_mul_map {X : Type} [Fintype X] (P : Matrix X X C) (A : Matrix X X R) (j : X) :
    (P * A.map (algebraMap R C)).col j = ∑ i, A i j • P.col i := by
  rw [Matrix.col_mul_eq_mulVec_col, Matrix.mulVec_eq_sum]
  simp only [Matrix.col, Matrix.transpose_apply, Matrix.map_apply, op_smul_eq_smul, algebraMap_smul]

private lemma cols_mul_lemma {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (h : Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j)) :
    ∃ A : Matrix X X R, Q = P * A.map (algebraMap R C) := by
  have hc : ∀ j, ∃ c : X → R, ∑ i, c i • (fun x => P x i) = fun x => Q x j := fun j =>
    (Submodule.mem_span_range_iff_exists_fun R).1 (h (Submodule.subset_span ⟨j, rfl⟩))
  choose c hc using hc
  let A : Matrix X X R := Matrix.of fun i j => c j i
  refine ⟨A, Matrix.ext fun x j => ?_⟩
  exact congrFun ((hc j).symm.trans (col_mul_map P A j).symm) x

theorem valuation_det_eq_of_span_eq_alt (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    {P Q : Matrix X X C} (hP : IsUnit P.det)
    (h : Submodule.span R (Set.range fun j x => P x j) =
      Submodule.span R (Set.range fun j x => Q x j)) :
    v Q.det = v P.det := by
  obtain ⟨A, hA⟩ := cols_mul_lemma (R := R) h.ge
  obtain ⟨B, hB⟩ := cols_mul_lemma (R := R) h.le
  have hdQ : Q.det = P.det * algebraMap R C A.det := by
    rw [hA, Matrix.det_mul, det_map_algebraMap]
  have hdP : P.det = Q.det * algebraMap R C B.det := by
    rw [hB, Matrix.det_mul, det_map_algebraMap]
  have hAB : algebraMap R C A.det * algebraMap R C B.det = 1 := by
    refine mul_left_cancel₀ hP.ne_zero ?_
    rw [← mul_assoc, ← hdQ, ← hdP, mul_one]
  have hvA : v (algebraMap R C A.det) = 1 :=
    eq_one_of_le_one_of_mul_eq_one (hv.map_le_one _) (hv.map_le_one _)
      (by rw [← map_mul v, hAB, map_one])
  rw [hdQ, map_mul, hvA, mul_one]

theorem exists_matrix_span_eq (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (M : Submodule R (X → C)) (hfg : M.FG)
    (hsp : Submodule.span C (M : Set (X → C)) = ⊤) :
    ∃ β : Matrix X X C, IsUnit β.det ∧ M = Submodule.span R (Set.range fun j x => β x j) := by
  classical
  obtain ⟨S, rfl⟩ := hfg
  rw [Submodule.span_span_of_tower] at hsp
  suffices key : ∀ (n : ℕ) (S : Finset (X → C)), S.card = n →
      Submodule.span C (↑S : Set (X → C)) = ⊤ →
      ∃ β : Matrix X X C, IsUnit β.det ∧
        Submodule.span R (↑S : Set (X → C)) = Submodule.span R (Set.range fun j x => β x j) from
    key _ S rfl hsp
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro S hn hspC
  by_cases hli : LinearIndependent C (fun i : S => (i : X → C))
  · have hb := Module.Basis.mk hli (by simpa using hspC.ge)
    let e : X ≃ S := (hb.indexEquiv (Pi.basisFun C X)).symm
    refine ⟨Matrix.of fun x j => ((e j : S) : X → C) x, ?_, ?_⟩
    · refine (Matrix.isUnit_iff_isUnit_det _).1 (Matrix.linearIndependent_cols_iff_isUnit.1 ?_)
      exact hli.comp e e.injective
    · congr 1
      ext f
      constructor
      · intro hf
        exact ⟨e.symm ⟨f, hf⟩, by ext x; simp⟩
      · rintro ⟨j, rfl⟩
        exact (e j).2
  · obtain ⟨g, hg, i1, hi1⟩ := Fintype.not_linearIndependent_iff.1 hli
    obtain ⟨i0, -, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => v (g i))
      ⟨i1, Finset.mem_univ _⟩
    have hg0 : g i0 ≠ 0 := by
      intro h0
      have h2 := hmax i1 (Finset.mem_univ _)
      rw [h0, map_zero] at h2
      exact hi1 ((Valuation.zero_iff v).1 (le_antisymm h2 zero_le))
    have key : (i0 : X → C) =
        ∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C) := by
      have h1 := Finset.add_sum_erase Finset.univ (fun i => g i • (i : X → C)) (Finset.mem_univ i0)
      rw [hg] at h1
      have h2 : g i0 • (i0 : X → C) = -∑ i ∈ Finset.univ.erase i0, g i • (i : X → C) :=
        eq_neg_of_add_eq_zero_left h1
      calc (i0 : X → C) = (g i0)⁻¹ • (g i0 • (i0 : X → C)) := by
            rw [smul_smul, inv_mul_cancel₀ hg0, one_smul]
        _ = _ := by
          rw [h2, smul_neg, Finset.smul_sum, ← Finset.sum_neg_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [smul_smul, neg_smul, mul_comm]
    have hle1 : ∀ i, v (-(g i * (g i0)⁻¹)) ≤ 1 := by
      intro i
      rw [Valuation.map_neg, map_mul, map_inv₀]
      calc v (g i) * (v (g i0))⁻¹ ≤ v (g i0) * (v (g i0))⁻¹ :=
            mul_le_mul_of_nonneg_right (hmax i (Finset.mem_univ _)) zero_le
        _ = 1 := mul_inv_cancel₀ ((Valuation.ne_zero_iff v).2 hg0)
    choose r hr using fun i => hv.exists_of_le_one (hle1 i)
    have hx0R : (i0 : X → C) ∈ Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      have hsum : (∑ i ∈ Finset.univ.erase i0, (-(g i * (g i0)⁻¹)) • (i : X → C)) ∈
          Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
        refine Submodule.sum_mem _ fun i hi => ?_
        rw [← hr i, algebraMap_smul]
        refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
        exact Finset.mem_coe.2 (Finset.mem_erase.2
          ⟨fun h => (Finset.mem_erase.1 hi).1 (Subtype.ext h), i.2⟩)
      rw [← key] at hsum
      exact hsum
    have hx0C : (i0 : X → C) ∈ Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) :=
      Submodule.span_le_restrictScalars R C _ hx0R
    have hS : (↑S : Set (X → C)) = insert (i0 : X → C) ↑(S.erase (i0 : X → C)) := by
      rw [← Finset.coe_insert, Finset.insert_erase i0.2]
    have hspR : Submodule.span R (↑S : Set (X → C)) =
        Submodule.span R (↑(S.erase (i0 : X → C)) : Set (X → C)) := by
      rw [hS, Submodule.span_insert_eq_span hx0R]
    have hspC' : Submodule.span C (↑(S.erase (i0 : X → C)) : Set (X → C)) = ⊤ := by
      rw [← hspC, hS, Submodule.span_insert_eq_span hx0C]
    obtain ⟨β, hβ, hβS⟩ := ih _ (by rw [← hn]; exact Finset.card_erase_lt_of_mem i0.2)
      (S.erase (i0 : X → C)) rfl hspC'
    exact ⟨β, hβ, hspR.trans hβS⟩

private lemma cols_le_lemma_2 {X : Type} [Fintype X] [DecidableEq X] {P Q : Matrix X X C}
    (A : Matrix X X R) (hA : Q = P * A.map (algebraMap R C)) :
    Submodule.span R (Set.range fun j x => Q x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  change Q.col j ∈ _
  rw [hA, col_mul_map]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem inv_mem_of_valuation_eq_one (hv : v.Integers R) {X : Type} [Fintype X] [DecidableEq X]
    (A : Submodule R (X → C)) (P : Matrix X X C) (hP : IsUnit P.det)
    (hA : A = Submodule.span R (Set.range fun j x => P x j))
    (one : (1 : X → C) ∈ A) (mul : ∀ f g, f ∈ A → g ∈ A → f * g ∈ A)
    (u : X → C) (hu : u ∈ A) (hunit : ∀ x, v (u x) = 1) : u⁻¹ ∈ A := by
  have hu0 : ∀ x, u x ≠ 0 := fun x h0 => by simpa [h0] using hunit x
  have hPA : ∀ j, (fun x => P x j) ∈ A := fun j => by
    rw [hA]; exact Submodule.subset_span ⟨j, rfl⟩
  have hcolD : ∀ j, (fun x => (Matrix.diagonal u * P) x j) = u * fun x => P x j := by
    intro j; ext x; simp [Matrix.diagonal_mul]
  have hDle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      Submodule.span R (Set.range fun j x => P x j) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    show (fun x => (Matrix.diagonal u * P) x j) ∈ Submodule.span R _
    rw [hcolD, ← hA]
    exact mul u _ hu (hPA j)
  obtain ⟨T, hT⟩ := cols_mul_lemma hDle
  have hdT : algebraMap R C T.det = ∏ x, u x := by
    have e := congrArg Matrix.det hT
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, det_map_algebraMap] at e
    exact mul_left_cancel₀ hP.ne_zero (by rw [← e]; ring)
  have hvT : v (algebraMap R C T.det) = 1 := by
    rw [hdT, map_prod]
    exact Finset.prod_eq_one fun x _ => hunit x
  have hTu : IsUnit T.det := (hv.isUnit_iff_valuation_eq_one).mpr hvT
  have hPD : P = (Matrix.diagonal u * P) * (T⁻¹).map (algebraMap R C) := by
    rw [hT, Matrix.mul_assoc, ← Matrix.map_mul, Matrix.mul_nonsing_inv T hTu]
    simp
  have hPle := cols_le_lemma_2 _ hPD
  have hmem : (1 : X → C) ∈
      Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) :=
    hPle (by rw [← hA]; exact one)
  have hle : Submodule.span R (Set.range fun j x => (Matrix.diagonal u * P) x j) ≤
      A.comap (LinearMap.mulLeft R u⁻¹) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    rw [SetLike.mem_coe, Submodule.mem_comap, LinearMap.mulLeft_apply]
    convert hPA j using 1
    ext x
    simp [Matrix.diagonal_mul, hu0 x]
  simpa using hle hmem

end ReciprocityTheory.PGsh.L2
