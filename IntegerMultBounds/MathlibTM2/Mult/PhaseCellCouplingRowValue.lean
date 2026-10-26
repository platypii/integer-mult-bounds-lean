module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingInputWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingCoefficientWords
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRowAccumulator

/-! Structural data model for consecutive residual/recovery row results. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

def couplingRowWord {s : ℕ} [NeZero s] (P q t u band a b i : ℕ) (boundary : Bool)
    (C : ZMod s → GaussianInt) (rhs : GaussianInt) : GaussianInt :=
  rhs-(List.zipWith (fun x z => tdivN q (x*z)) (couplingInputWords boundary t band a b i C)
    (couplingCoefficientWords P q s t u band i)).sum

def couplingRowWords {s : ℕ} [NeZero s] (P q t u band a b : ℕ) (boundary : Bool)
    (C : ZMod s → GaussianInt) (i : ℕ) : List GaussianInt → List GaussianInt
  | [] => []
  | rhs::rest => couplingRowWord P q t u band a b i boundary C rhs ::
      couplingRowWords P q t u band a b boundary C (i+1) rest

@[simp] theorem couplingRowWords_length {s : ℕ} [NeZero s] (P q t u band a b i : ℕ)
    (boundary : Bool) (C : ZMod s → GaussianInt) (xs : List GaussianInt) :
    (couplingRowWords P q t u band a b boundary C i xs).length = xs.length := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simpa only [couplingRowWords,List.length_cons] using congrArg Nat.succ (ih (i+1))

theorem couplingRowWords_getElem {s : ℕ} [NeZero s] (P q t u band a b i : ℕ)
    (boundary : Bool) (C : ZMod s → GaussianInt) (xs : List GaussianInt) (n : ℕ) (hn : n < xs.length) :
    (couplingRowWords P q t u band a b boundary C i xs)[n]'(by simpa using hn) =
      couplingRowWord P q t u band a b (i+n) boundary C xs[n] := by
  induction xs generalizing i n with
  | nil => simp at hn
  | cons x xs ih =>
    cases n with
    | zero => simp [couplingRowWords]
    | succ n =>
      have h := ih (i+1) n (by simpa using hn)
      simpa only [couplingRowWords,List.getElem_cons_succ,Nat.add_assoc,Nat.add_comm 1] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
