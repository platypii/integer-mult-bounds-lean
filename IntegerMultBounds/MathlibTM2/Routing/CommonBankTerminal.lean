module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterBank
public import IntegerMultBounds.MathlibTM2.Host.EmbedStream

/-! Terminal execution on the common bulk/terminal bank preserves every tape
outside the terminal embedding, including all bulk-only metadata. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

theorem commonBankTerminal_exec {Q K : ℕ} {P P' U : Type} (extra : ℕ)
    (body : P → Pr P canonicalTerminalT Q (prime + K) U)
    (outerBody : P' → Pr P' (canonicalRouterCommonT + extra) Q (prime + K) U) (ι : P → P')
    (hbody : ∀ f, outerBody (ι f) = embProg (canonicalRouterTerminalLift extra) ι (body f))
    (n rows B L Lb : ℕ) (hstride : canonicalRouterStride n ≤ n)
    (mate : Fin n → Fin n) (hinv : Function.Involutive mate) (k : Fin 3) (reverse : Bool)
    (hn0 : 0 < n) (hn : n < 2 ^ L) (hBin : B < 2 ^ Lb) (hnB : n ≤ B)
    (hrows : 0 < rows) (hB : 1 ≤ B)
    (rowBits : List Bool) (hrow : GrowingCounterData.Canonical rowBits) (hrowNe : rowBits ≠ [])
    (hrowValue : Counter.value rowBits = rows)
    (hQ : swapStates selectiveSwapHd selectiveSwapPay selectiveSwapHd_inj ≤ Q)
    (v : HS (canonicalRouterCommonT + extra) Q (prime + K) U) (S : Stacks (canonicalRouterCommonT + extra) (prime + K))
    (hleft : ∀ j, S.L ((canonicalRouterTerminalLift extra) j) = [])
    (l : List (List (Fin (prime + K + 4)))) (hl : l.length = rows * 2 ^ n)
    (hlB : ∀ r ∈ l, r.length = B) (h8 : ∀ r ∈ l, ∀ x ∈ r, x.val < 8)
    (hbank : ∀ j, S.R ((canonicalRouterTerminalLift extra) j) =
      canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
        (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L
          (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse)) n L Lb B rowBits j) :
    ∃ (v' : HS (canonicalRouterCommonT + extra) Q (prime + K) U) (steps : ℕ), v'.user = v.user ∧
      (steps : ℝ) ≤ canonicalTerminalPrice n rows B L Lb rowBits.length
        (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse).length ∧
      Exec outerBody (embProg (canonicalRouterTerminalLift extra) ι (canonicalTerminalProgram hQ n rows B Lb rowBits.length))
        (mk v S) steps (mk v' { S with R := Function.update S.R (Fin.castAdd extra (canonicalRouterBulkEmbed (originalMatchingScheduleStream 6))) (moveRecs (canonicalRouterTerminalPerm n hstride mate hinv k reverse rows) l).flatten }) := by
  let words := canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
    (canonicalTerminalAux 0) l.flatten (elementaryCoordinateFrames L
      (canonicalRouterTerminalCoordinates n hstride mate hinv k reverse)) n L Lb B rowBits
  have hproject : embStk (canonicalRouterTerminalLift extra) S =
      (⟨S.inp, S.out, fun j => S.L ((canonicalRouterTerminalLift extra) j), words⟩ : Stacks canonicalTerminalT (prime + K)) :=
    congrArg (fun R => (⟨S.inp, S.out, fun j => S.L ((canonicalRouterTerminalLift extra) j), R⟩ :
      Stacks canonicalTerminalT (prime + K))) (funext hbank)
  obtain ⟨u, steps, hu, hm, he⟩ := canonicalTerminalCore_exec body S.inp S.out
    (fun j => S.L ((canonicalRouterTerminalLift extra) j)) hleft n rows B L Lb hstride mate hinv k reverse
    hn0 hn hBin hnB hrows hB rowBits hrow hrowNe hrowValue hQ
    (embDn (canonicalRouterTerminalLift extra) v) l hl hlB h8
  change Exec body _ (mk _ (⟨S.inp, S.out, fun j => S.L ((canonicalRouterTerminalLift extra) j), words⟩ :
    Stacks canonicalTerminalT (prime + K))) steps _ at he
  rw [← hproject] at he
  obtain ⟨v', hv, hexec⟩ := exec_emb_stream (canonicalRouterTerminalLift extra) (canonicalRouterTerminalLift_injective extra)
    ι body outerBody hbody (canonicalTerminalProgram hQ n rows B Lb rowBits.length) v S u steps
    (canonicalTerminalRouter .str) _ he
  rw [canonicalRouterTerminalLift_stream] at hexec
  dsimp only [embDn] at hu
  exact ⟨v', steps, hv.trans hu, hm, hexec⟩

end
end IntegerMultBounds.MathlibTM2.Routing
