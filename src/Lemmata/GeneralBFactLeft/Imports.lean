module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Fintype.Defs
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
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
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
import Mathlib.Topology.Sheaves.Init
public import Mathlib.Algebra.CharP.Basic
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.Algebra.Polynomial.Degree.Defs
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.Algebra.Polynomial.Eval.Defs
public import Mathlib.FieldTheory.Finite.Basic

@[expose] public section

namespace Bl.general_b_fact_left

theorem goal1 :
  ∀ {k : Type} [inst : Field.{0} k] [Fintype.{0} k] (t m e : k),
  Ne.{1} (HSub.hSub.{0, 0, 0} (HPow.hPow.{0, 0, 0} t 2) (HMul.hMul.{0, 0, 0} 4 m)) 0 →
    Exists.{1} fun (x : k) ↦
      Exists.{1} fun (y : k) ↦
        Eq.{1}
          (HAdd.hAdd.{0, 0, 0}
            (HAdd.hAdd.{0, 0, 0} (HPow.hPow.{0, 0, 0} x 2) (HMul.hMul.{0, 0, 0} (HMul.hMul.{0, 0, 0} t x) y))
            (HMul.hMul.{0, 0, 0} m (HPow.hPow.{0, 0, 0} y 2)))
          e := by
  intro k _ _ t m e hd
  by_cases hc : ringChar k = 2
  · have h2 : (2 : k) = 0 := by
      simpa only [hc, Nat.cast_ofNat] using ringChar.Nat.cast_ringChar (R := k)
    have h4 : (4 : k) = 0 := by
      rw [show (4 : k) = 2 * 2 by norm_num, h2, zero_mul]
    have ht : t ≠ 0 := fun h => hd (by simp [h, h4])
    by_cases hm : m = 0
    · refine ⟨1, (e - 1) / t, ?_⟩
      rw [hm]
      field_simp
      ring
    · obtain ⟨r, hr⟩ := (FiniteField.isSquare_of_char_two hc (e / m)).exists_sq
      exact ⟨0, r, by simpa [← hr] using mul_div_cancel₀ e hm⟩
  · have h2 : (2 : k) ≠ 0 := Ring.two_ne_zero hc
    have h4 : (4 : k) ≠ 0 := by
      rw [show (4 : k) = 2 * 2 by norm_num]
      exact mul_ne_zero h2 h2
    let D : k := -(t ^ 2 - 4 * m) / 4
    have hD : D ≠ 0 := div_ne_zero (neg_ne_zero.mpr hd) h4
    obtain ⟨a, b, hab⟩ := FiniteField.exists_root_sum_quadratic
      (Polynomial.degree_X_pow_sub_C (by decide : 0 < 2) e)
      (Polynomial.degree_C_mul_X_pow 2 hD) (FiniteField.odd_card_of_char_ne_two hc)
    simp only [Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C,
      Polynomial.eval_mul] at hab
    refine ⟨a - t * b / 2, b, ?_⟩
    have key : a ^ 2 + D * b ^ 2 = e := by linear_combination hab
    rw [← key]
    dsimp [D]
    field_simp
    ring

end Bl.general_b_fact_left
