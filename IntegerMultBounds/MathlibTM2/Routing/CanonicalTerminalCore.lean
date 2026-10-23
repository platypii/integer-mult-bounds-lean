module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalRouting
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalWords

/-! A stream-independent terminal core contract for the existing framed loader. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

def canonicalTerminalProgram {Q K : ℕ} {P U : Type}
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (n rows B Lb rowLength : ℕ) : Pr P canonicalTerminalT Q (prime + K) U :=
  sharedInputRoutingProgram canonicalTerminalInput
    (elementarySharedProgram canonicalTerminalRouter (sharedInputConfig canonicalTerminalInput)
      (canonicalTerminalAux 3) (canonicalTerminalAux 4) (canonicalTerminalAux 5)
      Lb (n + rowLength) B (rows * 2 ^ n)
      (compiledElementaryProgram canonicalTerminalCompiler (canonicalTerminalAux 0) (canonicalTerminalAux 1)
        canonicalTerminalRouter canonicalTerminalRouter_injective selectiveSwapHd selectiveSwapPay
        selectiveSwapHd_inj hQ canonicalTerminalT_fit (canonicalTerminalAux 2)))

def canonicalTerminalPrice (n rows B L Lb rowLength count : ℕ) : ℝ :=
  (L * (4 * n + 11) + 22 * n + 6 * rowLength + 46 : ℕ) + ((Lb * (4 * B + 11) + (n + rowLength) * (4 * (rows * 2 ^ n) + 11) + 2 * B + 2 * (rows * 2 ^ n) + 10 * n + 24 : ℕ) +
        ((count : ℝ) *
          ((elementaryCompileBase n L Lb rowLength + 7 * (rowLength + 3 * n + Lb + 11) + 4 * L + 6 : ℕ) +
            canonicalTerminalBaseCost n rows B + 2 +
            (12 * swapT 6 + 22 : ℕ) * (rowLength + 3 * n + Lb + 11 : ℕ)) + 10) +
        (2 * B + 2 * (rows * 2 ^ n) + 4 * n + 9 : ℕ)) +
        (6 * n + 2 * rowLength + 7 : ℕ)

theorem canonicalTerminalCore_exec {Q K : ℕ} {P U : Type}
    (body : P → Pr P canonicalTerminalT Q (prime + K) U)
    (inp : List (Bool ⊕ Bool)) (out : List Bool)
    (left : Fin canonicalTerminalT → List (Fin (prime + K + 4))) (hleft : ∀ j, left j = [])
    (n rows B L Lb : ℕ) (hstride : canonicalRouterStride n ≤ n)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (k : Fin 3) (reverse : Bool)
    (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (v : HS canonicalTerminalT Q (prime + K) U)
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8) :
    let cs := canonicalRouterTerminalCoordinates n hstride mate hinv k reverse
    let S : Stacks canonicalTerminalT (prime + K) :=
      ⟨inp, out, left, canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
        (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L cs) n L Lb B rowBits⟩
    ∃ (v' : HS canonicalTerminalT Q (prime + K) U) (m : ℕ), v'.user = v.user ∧
      (m : ℝ) ≤ canonicalTerminalPrice n rows B L Lb rowBits.length cs.length ∧
      Exec body (canonicalTerminalProgram hQ n rows B Lb rowBits.length) (mk v S) m
        (mk v' { S with R := Function.update S.R (canonicalTerminalRouter .str) (moveRecs (canonicalRouterTerminalPerm n hstride mate hinv k reverse rows) l).flatten }) := by
  dsimp only
  obtain ⟨ds, v', m, hk, hu, hm, he, hc, hb⟩ := canonicalRouterTerminal_exec body inp out left hleft
    n rows B L Lb hstride mate hinv k reverse hn0 hn hBin hnB hrows hB
    rowBits hrow hrowNe hrowValue hQ v l hl hlB h8
  rw [canonicalTerminalBaseCost_eq] at hm
  exact ⟨v', m, hu, hm, he⟩

end
end IntegerMultBounds.MathlibTM2.Routing
