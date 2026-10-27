module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCouplingGuard
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRowField

/-! Observed coupling rows: skipped residual values are irrelevant off the boundary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.ShortConv

def guardedCouplingRowWord {s : ℕ} [NeZero s] (P q t u band a b i : ℕ) (boundary : Bool)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt) : GaussianInt :=
  if couplingSkipAt boundary s t band a b i then rhs else
    couplingRowWord P q t u band a b i boundary C rhs

def guardedCouplingRowWords {s : ℕ} [NeZero s] (P q t u band a b : ℕ) (boundary : Bool)
    (C : ZMod s → GaussianInt) (i : ℕ) : List GaussianInt → List GaussianInt
  | [] => []
  | rhs::rest => guardedCouplingRowWord P q t u band a b i boundary C rhs ::
      guardedCouplingRowWords P q t u band a b boundary C (i+1) rest

@[simp] theorem guardedCouplingRowWords_length {s : ℕ} [NeZero s] (P q t u band a b i : ℕ)
    (boundary : Bool) (C : ZMod s → GaussianInt) (xs : List GaussianInt) :
    (guardedCouplingRowWords P q t u band a b boundary C i xs).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simpa only [guardedCouplingRowWords,List.length_cons] using congrArg Nat.succ (ih (i+1))

theorem guardedCouplingRowWords_getElem {s : ℕ} [NeZero s] (P q t u band a b i : ℕ)
    (boundary : Bool) (C : ZMod s → GaussianInt) (xs : List GaussianInt) (n : ℕ) (hn : n < xs.length) :
    (guardedCouplingRowWords P q t u band a b boundary C i xs)[n]'(by simpa using hn) =
      guardedCouplingRowWord P q t u band a b (i+n) boundary C xs[n] := by
  induction xs generalizing i n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => simp [guardedCouplingRowWords]
    | succ n =>
      have h := ih (i+1) n (by simpa using hn)
      simpa only [guardedCouplingRowWords,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using h


theorem couplingSkipAt_not_boundary {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (band a b i : ℕ) (hb : b ≤ s) (hi : i < s)
    (hskip : couplingSkipAt boundary s t band a b i = true) :
    (i : ZMod s) ∉ haloBoundary s t band a b := by
  have hzero := couplingSkipAt_sound hst boundary band a b i hb hi hskip
  have hd := recoveryZeroRows_stencil_disjoint hst.le band a b (i : ZMod s) hzero
    (δ := 0) (by simp [spatialCouplingOffsets])
  simpa using hd

theorem guardedCouplingRowWord_eq {s t : ℕ} [NeZero s] (hst : s < t)
    (P q u band a b i : ℕ) (boundary : Bool) (hb : b ≤ s) (hi : i < s)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt)
    (hobserved : boundary = true ∨ (i : ZMod s) ∈ haloBoundary s t band a b) :
    guardedCouplingRowWord P q t u band a b i boundary C rhs =
      couplingRowWord P q t u band a b i boundary C rhs := by
  unfold guardedCouplingRowWord
  split
  · rename_i hskip
    cases boundary with
    | false => exact False.elim ((couplingSkipAt_not_boundary hst false band a b i hb hi hskip)
        (hobserved.resolve_left (by decide)))
    | true =>
      symm
      apply couplingRowWord_zero_window
      intro δ hδ
      exact couplingZeroRows_stencil_disjoint hst.le true band a b i
        (couplingSkipAt_sound hst true band a b i hb hi hskip) hδ
  · rfl

def guardedCouplingRowField {s : ℕ} [NeZero s] (P q t u band a b : ℕ) (boundary : Bool)
    (C B : ZMod s → GaussianInt) (i : ZMod s) : GaussianInt :=
  guardedCouplingRowWord P q t u band a b i.val boundary C (B i)

theorem guardedCouplingRowWords_eq_chirpLine {s : ℕ} [NeZero s] (P q t u band a b : ℕ)
    (boundary : Bool) (C B : ZMod s → GaussianInt) :
    guardedCouplingRowWords P q t u band a b boundary C 0 (chirpLine s B) =
      chirpLine s (guardedCouplingRowField P q t u band a b boundary C B) := by
  apply List.ext_getElem (by simp)
  intro j hj hj'
  have hjs : j < s := by simpa using hj
  rw [guardedCouplingRowWords_getElem P q t u band a b 0 boundary C (chirpLine s B) j (by simpa using hjs)]
  simp [chirpLine,guardedCouplingRowField,Nat.mod_eq_of_lt hjs]

theorem guardedCouplingRowField_eq {s t : ℕ} [NeZero s] (hst : s < t)
    (P q u band a b : ℕ) (boundary : Bool) (hb : b ≤ s)
    (C B : ZMod s → GaussianInt) (i : ZMod s)
    (hobserved : boundary = true ∨ i ∈ haloBoundary s t band a b) :
    guardedCouplingRowField P q t u band a b boundary C B i =
      couplingRowField P q t u band a b boundary C B i := by
  exact guardedCouplingRowWord_eq hst P q u band a b i.val boundary hb i.val_lt C (B i)
    (by simpa using hobserved)

theorem guardedCouplingRowField_norm {s t p u q band a b rhsExp inputExp countExp : ℕ} [NeZero s] {α d : ℝ}
    (boundary : Bool) (hp : 0 < p) (hst : s < t) (hαu : α^2 = (u : ℝ))
    (hθ : 0 < (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (C B : ZMod s → GaussianInt) (hcount : 2*band+1 ≤ 2^countExp)
    (hB : ∀ j, ‖value q (B j)‖ ≤ (2 : ℝ)^rhsExp)
    (hC : ∀ j ∈ (if boundary then PhaseCellDiscreteGeometry.haloBoundary s t band a b
        else PhaseCellDiscreteGeometry.haloInterior s t band a b), ‖value q (C j)‖ ≤ (2 : ℝ)^inputExp)
    (i : ZMod s) :
    ‖value q (guardedCouplingRowField (2^15*p) q t u band a b boundary C B i)‖ ≤
      (2 : ℝ)^couplingRowExponent rhsExp inputExp (8*p+1) countExp := by
  unfold guardedCouplingRowField guardedCouplingRowWord
  split
  · exact (hB i).trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (by unfold couplingRowExponent; omega))
  · exact couplingRowField_norm boundary hp hst hαu hθ hgap hbudget C B hcount hB hC i

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
