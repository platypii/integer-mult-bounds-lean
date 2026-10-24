module

public import IntegerMultBounds.MathlibTM2.Routing.IndexedCountBank

/-! Initializing the binary index and rewinding the count archive closes the
indexed bank invariant, leaving only accumulated profile output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

theorem indexedCountBank_zero (R : Fin T → List (Fin (A + 4)))
    (count saved index dst : Fin T) (hreg : [count,saved,index,dst].Nodup)
    (L : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4))) (hcount : R count = cs) :
    indexedCountBank R count saved index dst L cs profile 0 = Function.update R index (binSyms L 0) := by
  have hn := hreg
  regs_ne hn
  funext j
  by_cases hc : j = count
  · subst j; simp [indexedCountBank, indexedCountOutput, hcount, ‹count ≠ saved›, ‹count ≠ index›, ‹count ≠ dst›]
  by_cases hs : j = saved
  · subst j; simp [indexedCountBank, indexedCountOutput, ‹saved ≠ index›, ‹saved ≠ dst›]
  by_cases hi : j = index
  · subst j; simp [indexedCountBank, indexedCountOutput, ‹index ≠ dst›]
  by_cases hd : j = dst
  · subst j; simp [indexedCountBank, indexedCountOutput, (Ne.symm ‹index ≠ dst›)]
  · simp [indexedCountBank, indexedCountOutput, hc, hs, hi, hd]

theorem indexedCountBank_clean (R : Fin T → List (Fin (A + 4)))
    (count saved index dst : Fin T) (hreg : [count,saved,index,dst].Nodup)
    (L : ℕ) (cs : List (Fin (A + 4))) (profile : ℕ → List (Fin (A + 4)))
    (hcount : R count = cs) (hsaved : R saved = []) (hindex : R index = []) :
    let B := indexedCountBank R count saved index dst L cs profile cs.length
    let C := movedR B saved count id (B saved)
    Function.update C index [] =
      Function.update R dst (indexedCountOutput profile cs.length ++ R dst) := by
  have hn := hreg
  regs_ne hn
  dsimp only
  funext j
  by_cases hc : j = count
  · subst j; simp [indexedCountBank, movedR, hcount, hsaved, ‹count ≠ saved›, ‹count ≠ index›, ‹count ≠ dst›, ‹saved ≠ index›, ‹saved ≠ dst›]
  by_cases hs : j = saved
  · subst j; simp [indexedCountBank, movedR, hsaved, (Ne.symm ‹count ≠ saved›), ‹saved ≠ index›, ‹saved ≠ dst›]
  by_cases hi : j = index
  · subst j; simp [hindex, ‹index ≠ dst›]
  by_cases hd : j = dst
  · subst j; simp [indexedCountBank, movedR, (Ne.symm ‹count ≠ dst›), (Ne.symm ‹saved ≠ dst›), (Ne.symm ‹index ≠ dst›)]
  · simp [indexedCountBank, movedR, hc, hs, hi, hd]

end IntegerMultBounds.MathlibTM2.Routing
