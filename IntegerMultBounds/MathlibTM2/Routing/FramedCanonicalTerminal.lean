module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalCore
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBulk

/-! The concrete terminal core uses the existing shared framed loader, with
metadata installation and erasure charged and the current stream supplied live. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem framedCanonicalTerminal_exec {Q K : ℕ} {P P' U : Type}
    (body : P → Pr P canonicalTerminalT Q (prime + K) U)
    (outerBody : P' → Pr P' (canonicalTerminalT + 3) Q (prime + K) U) (ι : P → P')
    (hbody : ∀ f, outerBody (ι f) = embProg (framedCoreEmbed canonicalTerminalT) ι (body f))
    (n rows B L Lb : ℕ) (hstride : canonicalRouterStride n ≤ n)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (k : Fin 3) (reverse : Bool)
    (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (rest : List (Fin (prime + K + 4)))
    (v : HS (canonicalTerminalT + 3) Q (prime + K) U) (S : Stacks (canonicalTerminalT + 3) (prime + K))
    (hleft : ∀ j, S.L (framedCoreEmbed canonicalTerminalT j) = [])
    (htmp : S.R (framedCoreAux canonicalTerminalT 1) = [])
    (hblank : ∀ j, j ≠ canonicalTerminalRouter .str → S.R (framedCoreEmbed canonicalTerminalT j) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hstream : S.R (framedCoreEmbed canonicalTerminalT (canonicalTerminalRouter .str)) = l.flatten)
    (hinput : S.R (framedCoreAux canonicalTerminalT 0) =
      delimitedBankFrames canonicalRouterDelimiter (framedCoreJobs (framedCoreEmbed canonicalTerminalT)
        (canonicalTerminalRouter .str)
        (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
          (canonicalTerminalAux 0) [] (elementaryCoordinateFrames L
            (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse)) n L Lb B rowBits)) ++ rest) :
    let cs := canonicalRouterTerminalCoordinates n hstride mate hinv k reverse
    let words := canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) [] (elementaryCoordinateFrames L cs) n L Lb B rowBits
    let frame := delimitedBankFrames canonicalRouterDelimiter
      (framedCoreJobs (framedCoreEmbed canonicalTerminalT) (canonicalTerminalRouter .str) words)
    let output := (moveRecs (canonicalRouterTerminalPerm n hstride mate hinv k reverse rows) l).flatten
    ∃ (v' : HS (canonicalTerminalT + 3) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalTerminalPrice n rows B L Lb rowBits.length cs.length +
        (6 * frame.length + 2 * (framedCoreJobs (framedCoreEmbed canonicalTerminalT)
          (canonicalTerminalRouter .str) words).length + 2 : ℕ) ∧
      Exec outerBody (framedCoreCallProgram (canonicalTerminalRouter .str) canonicalRouterDelimiter
        (fun x => decide (x.val < 8)) ι (canonicalTerminalProgram hQ n rows B Lb rowBits.length))
        (mk v S) steps (mk v' { S with R := delimitedCallAdvanced S.R (framedCoreAux canonicalTerminalT 0) (framedCoreAux canonicalTerminalT 2) (framedCoreEmbed canonicalTerminalT (canonicalTerminalRouter .str)) frame rest output }) := by
  dsimp only
  apply framedCoreCall_exec body outerBody ι hbody (canonicalTerminalRouter .str)
    canonicalRouterDelimiter (fun x => decide (x.val < 8)) (by rfl)
    (canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) [] (elementaryCoordinateFrames L
        (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse)) n L Lb B rowBits)
    ?_ rest _ v S hinput htmp hblank (canonicalTerminalProgram hQ n rows B Lb rowBits.length)
    (canonicalTerminalPrice n rows B L Lb rowBits.length
      (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse).length) ?_
  · intro j hj x hx
    exact decide_eq_true (canonicalTerminalRoutingBank_small [] (by simp) n L Lb B rowBits
      (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse) j x hx)
  · intro u
    dsimp only
    rw [hstream, canonicalTerminalRoutingBank_updateStream]
    exact canonicalTerminalCore_exec body _ _ _ hleft n rows B L Lb hstride mate hinv k reverse
      hn0 hn hBin hnB hrows hB rowBits hrow hrowNe hrowValue hQ u l hl hlB h8

end
end IntegerMultBounds.MathlibTM2.Routing
