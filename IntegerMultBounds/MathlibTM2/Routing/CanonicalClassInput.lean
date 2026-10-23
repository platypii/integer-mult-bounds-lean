module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalClassExec

/-! Pure inputs and compact execution contract for one complete matching class.
The record equalities describe intermediate data; no execution is a field. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section
variable {Q K : ℕ} (n : ℕ) (hn : canonicalRouterStride n ≤ n)
    (R B : ℕ) (hR : 0 < R) (hB : 1 ≤ B) (mate : Fin n → Fin n) (hinv : Function.Involutive mate)
    (k : Fin 3)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q) (hA : 4 ≤ prime + K)

structure CanonicalClassInput where
  records : Fin 3 → List (List (Fin (prime + K + 4)))
  count : ∀ d, (records d).length = R * 2 ^ n
  shape : ∀ d, ∀ row ∈ records d, row.length = B ∧ ∀ x ∈ row, x.val < 8
  next₁ : records 1 = moveRecs
    (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k false hQ hA
      (records 0) (count 0) (shape 0) (List.finRange (canonicalRouterStride n))) (records 0)
  next₂ : records 2 = moveRecs
    (canonicalRouterDirectionalPerm n hn R B hR hB mate hinv k true hQ hA
      (records 1) (count 1) (shape 1) (List.finRange (canonicalRouterStride n))) (records 1)

variable {n hn R B hR hB mate hinv k hQ hA}
variable (input : CanonicalClassInput n hn R B hR hB mate hinv k hQ hA)
    (L Lb : ℕ) (rowBits : List Bool)

namespace CanonicalClassInput

def perm : Equiv.Perm (Fin (R * 2 ^ n)) :=
  canonicalRouterClassPerm n hn mate hinv k R B hR hB hQ hA (input.records 0) (input.count 0) (input.shape 0)

def directionFrame (d : Fin 3) : List (Fin (prime + K + 4)) :=
  canonicalDirectionalFrame n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
    (input.records d) (input.count d) (input.shape d) L Lb rowBits (List.finRange (canonicalRouterStride n))

def frame : List (Fin (prime + K + 4)) :=
  input.directionFrame L Lb rowBits 0 ++ (input.directionFrame L Lb rowBits 1 ++ input.directionFrame L Lb rowBits 2)

def directionProgram (d : Fin 3) : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  canonicalDirectionalProgram n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
    (input.records d) (input.count d) (input.shape d) Lb rowBits

def program : Pr Empty ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit :=
  .seq (.seq (input.directionProgram Lb rowBits 0) (input.directionProgram Lb rowBits 1))
    (input.directionProgram Lb rowBits 2)

def directionPrice (d : Fin 3) : ℝ :=
  canonicalDirectionalPrice n hn R B hR hB mate hinv k (decide (d = 1)) hQ hA
    (input.records d) (input.count d) (input.shape d) L Lb rowBits (List.finRange (canonicalRouterStride n))

def price : ℝ :=
  (input.directionPrice L Lb rowBits 0 + input.directionPrice L Lb rowBits 1) + input.directionPrice L Lb rowBits 2

theorem exec
    (hn0 : 0 < n) (hnfit : n < 2 ^ L) (hBfit : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = R)
    (rest : List (Fin (prime + K + 4)))
    (v : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit)
    (S : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K))
    (ready : FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B S)
    (hstream : S.R (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) = (input.records 0).flatten)
    (hinput : S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) = input.frame L Lb rowBits ++ rest) :
    let E : Stacks ((canonicalRouterCommonT + 3) + 3) (prime + K) :=
      { S with R := delimitedCallAdvanced S.R (framedCoreAux (canonicalRouterCommonT + 3) 0) (framedCoreAux (canonicalRouterCommonT + 3) 2) (framedCoreEmbed (canonicalRouterCommonT + 3) canonicalDirectionalStream) (input.frame L Lb rowBits) rest (moveRecs input.perm (input.records 0)).flatten }
    ∃ (v' : HS ((canonicalRouterCommonT + 3) + 3) Q (prime + K) Unit) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ input.price L Lb rowBits ∧
      FramedCoreReady canonicalDirectionalStream (R * 2 ^ n) B E ∧
      Exec Empty.elim (input.program Lb rowBits) (IntegerMultBounds.MathlibTM2.Host.mk v S) steps (IntegerMultBounds.MathlibTM2.Host.mk v' E) := by
  apply canonicalClass_exec n hn R B hR hB mate hinv k hQ hA
    (input.records 0) (input.count 0) (input.shape 0) L Lb rowBits
    (input.records 1) (input.records 2) (input.count 1) (input.count 2) (input.shape 1) (input.shape 2)
    hn0 hnfit hBfit hnB hrow hrowNe hrowValue input.next₁ input.next₂ rest v S ready hstream
  simpa [frame, directionFrame, List.append_assoc] using hinput

end CanonicalClassInput
end
end IntegerMultBounds.MathlibTM2.Routing
